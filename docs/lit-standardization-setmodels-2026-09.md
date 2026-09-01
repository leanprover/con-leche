# Literature report: standardization/residuals, confluence techniques, and set-theoretic models of DTT

Research split: Topics 1–2 done directly (PDFs downloaded and text-extracted with `pdftotext`; all quotes verbatim from those extractions). Topic 3 run by a parallel sub-agent, with Carneiro's thesis independently re-fetched and cross-checked by me (§3.1.1/§3.1.2 quotes match verbatim).

---

# TOPIC 1 — Standardization, labelled reduction, residuals

## 1(a) The lemma you are looking for exists, and it is called **RuS**

**This is the single most important finding of this report.**

### The exact statement of your "forward dichotomy"

**Jörg Endrullis & Roel de Vrijer, "Reduction under Substitution", RTA 2008, LNCS 5117, pp. 425–440.**
PDF: <http://joerg.endrullis.de/assets/papers/lambda-reduction-under-substitution-2008.pdf> (DOI 10.1007/978-3-540-70590-1_29; Springer page <https://link.springer.com/chapter/10.1007/978-3-540-70590-1_29>).

Abstract, verbatim:

> "The Reduction-under-Substitution Lemma (RuS), due to van Daalen [Daa80], provides an answer to the following question concerning the lambda calculus: given a reduction M[x := L] ↠ N, what can we say about the contribution of the substitution to the result N."

Introduction: *"how much of N can be produced already by M, independently of the substitution? The answer to the second question will turn out to be: **a prefix of N**. Thus there is a natural inverse correspondence with the so-called prefix property."*

**Lemma 6 (Reduction under Substitution), §2, p. 6:**

> "Let M[x := L] ↠ N. Then there are a term N′, an n-hole context C (with n ≥ 0), x-vectors B₁,…,Bₙ and terms A₁,…,Aₙ, such that M ↠ N′ ≡ C[B₁,…,Bₙ], Bᵢ[x := L] ↠ Aᵢ for all 1 ≤ i ≤ n and N ≡ C[A₁,…,Aₙ]."

where an **x-vector** is a term `x P₁ … P_k` (k ≥ 0) — i.e. *a position headed by a substituted variable*. This is literally the dichotomy: the reduction of `t[θ]` splits into (i) a **core** reduction `M ↠ N′` that `t` itself performs, producing an x-free prefix context `C`, and (ii) reductions taking place **entirely at positions supplied by θ** (the x-vector holes). The decomposition is not unique; they define a coarser/finer ordering `C₁ ⊑ C₂` on prefixes.

**The weak-head specialisation you actually need — Lemma 7 (Square Brackets Lemma, van Daalen), §2, p. 7:**

> "Let M[x := L] ↠ λy.P. Then we have one of the following two cases.
> 1. M ↠ λy.P′ for a P′ such that P′[x := L] ↠ P
> 2. M ↠ xQ and (xQ)[x := L] ↠ λy.P
>
> Proof. The prefix C found by Lem. 6 can either be of the form λy.C′ or it must be the empty context. If C ≡ λy.C′ then N′ ≡ λy.P′ and we are in Case 1. If C ≡ [ ] then N′ is an x-vector and we are in Case 2."

That is exactly "either the core reaches a λ (mirroring), or the core gets stuck on a substituted variable and the λ came from θ". This is the theorem to port.

**Generalisations in the same paper, all directly relevant to a telescope setting:**

- **Theorem 13 (RuS for multiple substitution)**, §3 — `[x⃗ := L⃗]` simultaneously.
- **Corollary 1 (context filling), §5, p. 15** — handles **capture**: *"We extend reduction under multiple substitution to context filling; the difference being that variables of the arguments might get bound."* For `C[L₁,…,L_m] ↠ N`, with `y⃗ᵢ` the variables bound at hole i, one gets `C[x₁y⃗₁,…,x_my⃗_m] ↠ D[B₁,…,Bₙ] ⤳ N` under `[xᵢ := λy⃗ᵢ.Lᵢ]`.
- **Theorem 23, §6, p. 18** — the genericity-flavoured corollary: *"The prefix C is independent of the substitution, that is, for any P⃗ we have M[x⃗ := P⃗] ↠ C[…]"*, plus each hole depends on exactly one substituted term.

**Provenance:**
- van Daalen, *The Language Theory of Automath*, PhD thesis, TU Eindhoven, 1980 (large parts reproduced in Nederpelt–Geuvers–de Vrijer, *Selected Papers on Automath*, North-Holland 1994).
- **RuS is Exercise 15.4.8 in Barendregt's book** — stated verbatim in the RuS paper: *"RuS found its way into Barendregt's book on the λ-calculus [Bar84], where it ended up as Exercise 15.4.8. This literally seemed to be the end of the story, as subsequently little more attention has been paid in the literature to either BL or RuS."*
- **Barendregt's Lemma (Lemma 1, §1)** is the application-form variant (`FM ↠ N`), from Barendregt's 1972 unpublished note *Non-definability of δ*, Theorem 12 (quoted verbatim in the paper). Follows from RuS by taking `Fx` for M.
- Historical account: R.C. de Vrijer, "Barendregt's lemma", in *Reflections on Type Theory, Lambda Calculus, and the Mind*, Radboud University Nijmegen, 2007, pp. 275–284.
- Book treatment: **Barendregt & Manzonetto, *A Lambda Calculus Satellite*, College Publications 2022, §1.3 "RuS and consequences"** — confirmed from the ToC (<https://www.irif.fr/~gmanzone/papers/toc.pdf>) and the FSCD 2023 invited talk (<https://drops.dagstuhl.de/storage/00lipics/lipics-vol260-fscd2023/LIPIcs.FSCD.2023.3/LIPIcs.FSCD.2023.3.pdf>, §1: *"the Reduction under Substitution (RuS) technique by Diederik van Daalen [65], and its consequences [26]"*).

### The proof structure — and it is mechanisation-ready

The proof is **exactly the three-way case split**, packaged as a small inductive relation. Definition 8.7 + **Lemma 9** (§3, p. 9) characterise `M ⤳ N` ("M reduces to N with all the substitution's contribution absorbed"):

> "We have M ⤳ N if and only if one of the following four cases applies:
> (i) M is an x-vector with M* ↠ N
> (ii) M ≡ N ≡ y for some variable y with y ≢ x₁,…,y ≢ x_m
> (iii) M ≡ M₁M₂ and N = N₁N₂ with M₁ ⤳ N₁ and M₂ ⤳ N₂
> (iv) M ≡ λy.M′ and N ≡ λy.N′ with M′ ⤳ N′"

Then two lemmas do all the work:

- **Lemma 11** (`⤳` stable under substitution): `M ⤳ M′, N ⤳ N′ ⟹ M[y:=N] ⤳ M′[y:=N′]` (for `y` not among the `x⃗`).
- **Lemma 12** (commutation/postponement): `⤳ · ↠ ⊆ ↠ · ⤳`. Its proof is verbatim the case analysis you want:
  > "Assume ρ is entirely in C. Then we have M|ₚ ≡ (λy.M₁)M₂ → M₁[y := M₂] and N|ₚ ≡ (λy.N₁)N₂ → N₁[y := N₂] ≡ O|ₚ with M₁ ⤳ N₁, M₂ ⤳ N₂ by Lem. 9. Hence M₁[y := M₂] ⤳ N₁[y := N₂] for some context C′ by Lem. 11. …
  > **If ρ is below C, then it is contained in one of the x-vectors Bᵢ and 'absorbed' by ⤳**, that is, M ⤳_C O.
  > **Finally if ρ is neither in C nor below C, then C|ₚ ≡ [ ]C′.** Then M|ₚ is an x-vector since C ⋫ M and therefore M|ₚ₁ is an x-vector. Hence C[[ ]]ₚ ⋫ M and C ⊑ C[[ ]]ₚ by Lem. 10. Observe that ρ is below C[[ ]]ₚ, a case that we have already considered."

The third bullet **is** the created-redex-at-the-interface case, and the resolution is: *refine the prefix context* so the interface redex becomes "below C", i.e. absorbed into the θ-side. That is the trick.

Then `Theorem 13 (RuS)` = `M* ↠ N` ⟹ (Lemma 12, since `M ⤳ M*` trivially) `M ↠ C[B⃗] ⤳ N`.

### Lévy's redex-creation classification (the three cases), precisely

Canonical enumeration, with `[10] = J.-J. Lévy, "Réductions correctes et optimales dans le lambda-calcul", PhD thesis, Paris VII, 1978`, in **E. Bonelli & P. Barenbaum, "Superdevelopments for Weak Reduction", WRS'09, EPTCS 15 (2010), pp. 20–31, doi 10.4204/EPTCS.15.2**, <https://arxiv.org/pdf/1001.4429>, §1 p. 20, verbatim:

> "There are three ways in which a redex may be created in λ-calculus [10]:
> **I.** (λx.x) (λy.P) Q → (λy.P) Q
> **II.** (λx.λy.P) R Q → (λy.P{x := R}) Q
> **III.** (λx.C[x Q]) λy.P → C′[(λy.P)Q′], where C′ = C{x := λy.P} and Q′ = Q{x := λy.P}.
> A superdevelopment from M allows contraction of newly created redexes of type I and II (**i.e. upward creation**)."

**Case III is precisely the problem case**: substituting a λ for a variable in *applied* position creates a redex at the variable position, with the λ from the substitution and the argument `Q` from the core term. Note the terminology: I and II are the *upward* creations (created redex sits at a prefix of the contracted redex); **III is not upward** — which is exactly why superdevelopments don't cover it and why the backward direction fails.

The machine-checkable form is **Proposition 2.0.2 (Redex creation)**, §2 p. 22, a four-way case analysis "*proved by case analysis on the relative positions of p and q*". It adds a **Case IV specific to weak reduction**: `M = C₁[(λ*x.C₂[(λy.M₁)M₂]) Q]` where `x ∈ fv((λy.M₁′)M₂′)` — the created redex arises because substitution supplies a *free variable* that unblocks a weak redex. Their §1 example: "*In the reduction step (λx.I x) y → I y, where I = λx.x, the underlined redex is a new redex of type IV.*" Worth noting if your reduction is weak / closed under fewer contexts.

Accattoli & Guerrieri, *Open Call-by-Value (Extended Version)*, <https://arxiv.org/pdf/1609.00322>, §2.2, restate Lévy's count and add a CbV-only "type 4":

> "According to Lévy [20], in the ordinary CBN λ-calculus redexes can be created in 3 ways. Creations of type 1 take the following form ((λx.λy.t)r)s →β (λy.t{x←r})s where the redex involving λy and s has been created by the β-step. … In CBV there is another form of creation—of type 4—not considered by Lévy: (λx.t)((λy.v)v′) →βv (λx.t)(v{y←v′}), i.e. a reduction in the argument turns the argument itself into a value, creating a βv-redex."

(Their numbering differs from Bonelli–Barenbaum's; type 1 there = type II above. Cite Bonelli–Barenbaum for the clean I/II/III list.)

They also record the notion that carves out which creations superdevelopments cover: *"m-developments … in turn a special case of more famous superdevelopments, i.e. reduction sequences reducing only (residuals of) redexes in the original term plus creations of type 1 (m-developments) or type 1 and 2 (superdevelopments). Both m-developments and superdevelopments always terminate."*

### The sufficient condition under which the **backward** direction *does* hold

**Accattoli & Guerrieri, Open CbV extended version, Appendix, Lemma 42 (Substitution of Inert Terms Does Not Create β_f-Redexes):**

> "Let t, u be terms and i be an inert term. There is s ∈ Λ such that:
> 1. if t{x←i} →βλ u then t →βλ s and s{x←i} = u;
> 2. if t{x←i} →βi u then t →βi s and s{x←i} = u."

That is exactly backward simulation, and it holds because inert terms cannot supply a λ. Their §2.1 definition (p. 6):

> "Inert terms can be equivalently defined as i ::= x | i f … The main feature of an inert term is that it is open, normal and that **when plugged in a context it cannot create a redex**, hence the name (it is not a so-called neutral term because it might have redexes under abstractions). **In Grégoire and Leroy's presentation, inert terms are called accumulators** and fireballs are simply called values."

**Practical upshot for a kernel:** if the telescope entries θ are *neutral / stuck / accumulator-shaped* (fvars applied to arguments, opaque constants), backward simulation is a theorem, not a hope. The failing case is exactly and only when θ supplies a head λ (Lévy creation III). So the right statement to aim for is the *conditional* one: split θ into λ-headed and inert entries.

## 1(b) Mechanized precedents — residuals and labels are painful; everyone who can, avoids them

| Development | System | What | Cite |
|---|---|---|---|
| **Gérard Huet, "Residual theory in λ-calculus: a formal development", JFP 4(3):371–394, 1994** | **Coq** (V5.8, Gallina) | Full residual theory of β; **Prism Theorem**, **Lévy's Cube Lemma** ("a strong form of the parallel-moves lemma"), parallel moves ⟹ confluence. Shipped as a Coq standard library. | <https://www.cambridge.org/core/journals/journal-of-functional-programming/article/residual-theory-in-calculus-a-formal-development/10C9E95ABFCEEFD4F1CBAF2C800647AA> |
| **Eugene W. Stark, "Residuated Transition Systems", AFP, 28 Feb 2022 (maintained through Jan 2025)** | **Isabelle/HOL** | Abstract RTS framework with a partial residuation operation; instantiated to λ-calculus with **de Bruijn indices, where terms represent parallel reduction steps**. Yields Church–Rosser, **Finite Developments** (adapting de Vrijer's proof), **Standardization**, **Leftmost Reduction**. Sequel: *Residuated Transition Systems II: Categorical Properties*. | <https://www.isa-afp.org/entries/ResiduatedTransitionSystem.html> |
| **Andreas Abel, Abella standardization example, October 2009** | **Abella** | `standardization : {betas T T'} ⟹ {sred T T'}`, with `srefl`, **`ssubst` (standard reduction closed under substitution)**, `sappend`. Plotkin-style inductive `sred`; **no residuals**. | <https://abella-prover.org/examples/lambda-calculus/sred.html> |
| **Lancelot, Accattoli, Vemclefs, "Barendregt's Theory of the λ-Calculus, Refreshed and Formalized", ITP 2025, LIPIcs 352, art. 13** | **Abella** | Confluence, standardization, head factorization, head normalization, solvability, **genericity**, contextual equivalence. Code: <https://github.com/adrilancelot/Abella-lambda-Barendregt-theory> | <https://drops.dagstuhl.de/storage/00lipics/lipics-vol352-itp2025/LIPIcs.ITP.2025.13/LIPIcs.ITP.2025.13.pdf> |
| **Ferruccio Guidi, "Standardization and Confluence in Pure λ-Calculus Formalized for the Matita Theorem Prover", JFR 5(1), 2012** | **Matita** | "*a new approach recently introduced by Xi and refined by Kashima that, **avoiding the notion of development** and having a neat inductive structure, is particularly suited for formalization in theorem provers*" | <https://jfr.unibo.it/article/view/3392> |
| **Copes, Szasz, Tasistro, "Formalization in Constructive Type Theory of the Standardization Theorem … using Multiple Substitution"** | **Agda** | Kashima's inductive standard-reducibility relation; Stoughton multiple substitution; "*only structural induction over the syntax and the relations defined*". Code: <https://github.com/mcopes73/standardization-agda> | <https://arxiv.org/pdf/1807.01871> |
| **McKinna & Pollack, "Some Lambda Calculus and Type Theory Formalized", JAR 23(3-4):373–409** | **LEGO** | "*an abstract, simplified proof of standardization for beta reduction **that does not mention redex positions or residuals***" | <https://www.lfcs.inf.ed.ac.uk/reports/97/ECS-LFCS-97-359/ECS-LFCS-97-359.pdf> |
| **Gheri & Popescu, "Case Studies in Formal Reasoning About Lambda-Calculus: Semantics, Church-Rosser, Standardization and HOAS"** | **Isabelle/HOL** | CR + standardization for both CBN and CBV, following Takahashi and Plotkin. §6.2 surveys *all* prior CR/standardization mechanizations (Abella, Coq, HOL, LEGO, PVS, Twelf, Nominal Isabelle). | <https://arxiv.org/pdf/2107.11674> |
| **Ramos, Oliveira, de Queiroz, de Veras, "A Modular Lean 4 Framework for Confluence and Strong Normalization…", arXiv:2512.09280 (10 Dec 2025)** | **Lean 4** | Diamond/Takahashi, Newman, Hindley–Rosen; six case studies; **10,367 lines, 497 theorems, zero axioms/sorries**; complete de Bruijn substitution infrastructure incl. substitution composition. **No residuals, no standardization.** | <https://arxiv.org/abs/2512.09280> |

**Assessment (mine, grounded in the above):** Lévy labels have been mechanized essentially once, as residual structures (Huet 1994, Stark 2022). Everyone doing standardization since ~1997 (McKinna–Pollack, Xi, Loader, Kashima, Abel, Guidi, Copes et al., Lancelot et al.) *explicitly avoids* residuals and positions in favour of an inductive `⇝st` relation. **I found no mechanization of RuS or the Square Brackets Lemma in any prover.** Given that RuS's proof is three lemmas over a four-clause inductive relation, this looks like a tractable Lean development rather than a research project.

For labelled reduction over an *explicit-substitution* calculus (closer to a real kernel): **Barenbaum & Bonelli, "Optimality and the Linear Substitution Calculus", FSCD 2017, LIPIcs 84, art. 9** — "*We propose a notion of redex family obtained by adapting Lévy labels to support these two distinctive features [action at a distance and rewriting modulo]*", noting "*redex creation may take place at a distance*"; proved in Glauert & Khasidashvili's Deterministic Residual Structures. <https://drops.dagstuhl.de/storage/00lipics/lipics-vol084-fscd2017/LIPIcs.FSCD.2017.9/LIPIcs.FSCD.2017.9.pdf>

Abstract frameworks: Melliès, *Axiomatic Rewriting Theory* I (diagrammatic standardization), III (factorisation, CTCS'97 LNCS 1290), IV (stability, LICS'98), VI (residual theory revisited); Bethke–Klop–de Vrijer, "Descendants and origins in term rewriting", Inf. Comput. 159:59–124, 2000 (the "prefix property"); Terese, *Term Rewriting Systems*, CUP 2003, Ch. 8.

## 1(c) Would standardization give you the structured trace? Yes — with a hard caveat about η

The relevant result is not full standardization but **head factorization**. From Lancelot–Accattoli–Vemclefs (ITP 2025), §5:

> "Factorization: if t →*β u then t →*h · →*¬h u."

and "the head factorization theorem of the λ-calculus (**Theorem 11.4.6 in Barendregt's book**)" — quoted in Accattoli, Faggian, Guerrieri, *Factorize Factorization*, CSL 2021, §1.

**Theorem 7 (Head Normalization)**, ITP 2025 §5, is exactly the statement turning "reaches whnf" into "head reduction reaches it":

> "Let t be a term. If t →*β u and u does not →h-reduce then →h terminates on t."

They also isolate, as a contribution, **Corollary 12 (Extended head normalization)**, §8:

> "Let t be a term and t →*β u. Then t is head terminating if and only if u is head terminating."

(proof uses confluence). This is the "replace the awkward image run by a convenient one" move.

Their standardization is Plotkin/Xi/Loader/Abel-style, with an inductive `⇝st`:

> "Refreshed standard reduction sequence ⇝st: x ⇝st x | t ⇝st t′ ⟹ λx.t ⇝st λx.t′ | t ⇝st t′, u ⇝st u′ ⟹ tu ⇝st t′u′ | t →h u, u ⇝st u′ ⟹ t ⇝st u′"
> "**Theorem 8 (Standardization).** Let t be a term. If t →*β u then t ⇝st u."
> "Our formalization of standardization is the adaptation to the reasoning level of Abel's Abella development, who builds on Loader, who builds on Xi, who, in turn, builds on Plotkin. … Our proof of standardization, however, is remarkably simple."

**Caveat you must know before betting on this: head factorization is not modular, and βη breaks it.** Accattoli, Faggian, Guerrieri, *Factorize Factorization*, CSL 2021, LIPIcs 183, art. 6, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol183-csl2021/LIPIcs.CSL.2021.6/LIPIcs.CSL.2021.6.pdf>:

- §3: "*Factorization and confluence are independent properties. … **βη, which is confluent, does not verify head nor leftmost factorization**, even though both β and η – separately – do.*"
- **Example 4.6**, verbatim: "*consider the root linear swap: t := λx.(II)(Ix) →¬hβ λx.(II)x ↦η II =: s, where I := λz.z. Note that t has no →hη step, and so the two steps cannot be swapped. The reduction sequence above is a counter-example to both head and leftmost factorization for βη. Start with the head (and leftmost) redex II: λx.(II)(Ix) →hβη λx.I(Ix). From λx.I(Ix), there is no way to reach s.*"

That paper also gives the **modular tool** for a compound kernel reduction (β + δ + ι + proj + …): **Proposition 4.5 (A test for modular head factorization)** — `→β ∪ →γ` satisfies head factorization if (1) `Fact(→hγ, →¬hγ)`, (2) **root linear swap** `→¬hβ · ↦γ ⊆ →hγ · →*β`, (3) `↦γ` is substitutive — and "*Lemma 4.3 gives either a proof that the swap conditions hold, or a counter-example*". A decidable-by-hand checklist per rule that hands you the countermodel when it fails.

---

# TOPIC 2 — Confluence, parallel reduction, postponement

## 2(a) Takahashi's method and its substitution lemma (the forward direction)

**Masako Takahashi, "Parallel Reductions in λ-Calculus", Information and Computation 118(1):120–127, 1995.** Key point: "*In the case of β-reduction, the effect of a parallel reduction is the same as that of a 'complete development' which is defined by using 'residuals' of β-redexes. A nice feature of parallel reduction is that it can be defined **directly by induction on the structure of λ-terms without referring to residuals or other auxiliary notions**.*" (<https://scispace.com/papers/parallel-reductions-in-l-calculus-m4q48y6zoh>)

The forward substitution lemma, in mechanized form — **ITP 2025, Lemma 9 (Substitutivity of ⇒β)**:

> "If t ⇒β t′ and u ⇒β u′, then t{x←u} ⇒β t′{x←u′}"
> "The key property of ⇒β is its **substitutivity**, which is proved by decorating with indices the standard proof of the underlying substitutivity property for ⇒β."

There is **no dual inversion lemma for ⇒β in the literature that I found** — RuS (Topic 1) is the accepted substitute.

Takahashi also gives the parallel-reduction proof of head factorization; Accattoli et al. abstract it into two properties (ITP 2025 §5, formalized in Abella): **Merge** (`t ⇒¬h · →h u ⟹ t ⇒β u`) and **Split**, plus **Persistence** (`t →h u, t →¬h s ⟹ s →h r`).

## 2(b) Postponement, mechanized

**Nipkow/Berghofer, Isabelle `HOL-Proofs-Lambda`**, theory `Eta`: <https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/library/HOL/HOL-Proofs-Lambda/Eta.html>. Theorems: `eta_confluent`, `square_eta`, `square_beta_eta`, `confluent_beta_eta`, `eta_postponement'`, and **`eta_postponement`: `(sup beta eta)⇧* s t ⟹ (beta⇧* OO eta⇧*) s t`**. Supporting: `eta_subst`, `eta_par_beta`, `rtrancl_eta_Abs/AppL/AppR`.

Abstract theory: *Factorize Factorization* §2 — Hindley's **strong postponement** local test (Lemma 2.4), and its failure for β ("*It is instructive to examine strong postponement with respect to β reduction… To prove head factorization is not trivial precisely because SP fails*"). Their **linear swap** condition is the weaker, checkable replacement, and the technique is explicitly the factorization analogue of Hindley–Rosen for confluence.

## 2(c) How kernel verifications avoid backward simulation: **confluence-based inversion**

**Sozeau et al., "Touring the MetaCoq Project", arXiv:2107.07670, §3.2.3 "Confluence"**, verbatim:

> "To support inversion lemmas such as Π-type injectivity, we need to show that reduction is confluent. From this proof, it follows that **the abstract, undirected conversion relation T ≡ U is equivalent to reduction of the two sides to terms T′ and U′ that are in the syntactic α-cumulativity relation.** We extend here Takahashi's seminal refinement of the Tait/Martin-Löf's proof of confluence for λ-calculus."

Machinery: **Theorem 2.2 (Triangle property)** for an optimal parallel-reduction function ρ on *(context, term)* pairs — contexts are needed because of let-bindings and action at a distance ("*in one step of ρ, we might reduce a local definition abstraction, expand it in function position of an application and reduce the produced beta-redex*") — ⟹ diamond ⟹ confluence of ⇒ ⟹ confluence of →. Then: "*Using this characterization of cumulativity, we can easily show that it is a congruence and that it enjoys expected inversion lemmas: if two Π-types are convertible, then they both reduce to Π-types that are in the α-cumulativity relation.*" And: "**Confluence is crucial to show transitivity of the directed version.**"

Also from §3.2.2: "*Proving subject reduction … can be rather difficult in a setting where definitional equality is typed, as it usually requires a logical relation argument/model construction. However, the syntactic theory is relatively well-understood for PTS: one can first independently prove context conversion/cumulativity and injectivity of Π-types … to prove type preservation in the application case.*"

So the answer to "is there a known technique — use confluence + forward simulation, then analyse the join?" is **yes, and it is the dominant technique in verified kernels.** MetaCoq derives every inversion/injectivity fact this way rather than by inverting steps.

**But there is a second technique that fits your problem even better — Accattoli & Lancelot's proof of light genericity.**

**Accattoli & Lancelot, "Light Genericity", FoSSaCS 2024, LNCS 14574, pp. 24–46**, <https://hal.science/hal-04406343>. **Theorem 3.1**:

> "**Light genericity as substitution**: if t is a term and t{x←u} is h-normalizing then t{x←s} is h-normalizing."

The proof (p. 9) never inverts an image step:

> "1. It follows from Prop. 5 (precisely, via Lemma 4 in the Appendix), that if t{x←u} is h-normalizing then so is t. Then t →*h h for some h-normal h. Again, by stability of head reduction under substitutions, we have both t{x←u} →*h h{x←u} and t{x←s} →*h h{x←s}. Note that t{x←u} h-normalizing implies h{x←u} h-normalizing. By normal genericity (Prop. 6), h{x←s} is h-normal. Therefore, t{x←s} is h-normalizing."

The four moves, in order, are the recipe:

1. **Backward *termination*, not backward steps**: `t{x←u}` h-normalizing ⟹ `t` h-normalizing. Proved by *contraposition of forward simulation* — Lemma 4.2: "*If t is h-diverging then t{x←u} is h-diverging by stability of →h under substitution (Prop. 5).*"
2. **Run the core term to its own head normal form** `t →*h h`.
3. **Push forward through θ** using Prop. 5 (Head substitutivity: `t →*h u ⟹ t{x←s} →*h u{x←s}`) — your existing forward simulation.
4. **Only then** analyse the *structurally constrained* residue, by induction on the shape of the **core** normal form — Prop. 6 (Normal genericity): "*1. If r is a rigid term and r{x←u} is h-normalizing then r{x←s} is a rigid term. 2. If h is h-normal and h{x←u} is h-normalizing then h{x←s} is h-normal.*" — a 6-case induction.

You never classify an arbitrary image step. You need only: forward simulation, forward simulation of divergence, and an induction over core normal forms. Much smaller than a full residual theory.

The ITP 2025 formalization confirms this is Abella-scale work ("*[9] uses head normalization, our Abella proof does not*"); the hard part they report is **Takahashi's trick** (contexts → substitutions), isolated as **Lemma 14 (Disentangling)** and a `disentangling` inductive predicate. If your θ is genuinely a substitution (not a context with capture), you skip that entirely.

Older, complementary: **J. Kuper, "Proving the genericity lemma by leftmost reduction is simple", RTA 1995, LNCS 914** — the standardization/leftmost route to the same statement.

## 2(d) The modern framing of "what a conversion checker certification needs"

**Meven Lennon-Bertrand, "What does it take to certify a conversion checker?", FSCD 2025, LIPIcs; extended version arXiv:2502.15500v3.** Code: <https://github.com/CoqHott/logrel-coq/tree/fscd25>. The most directly applicable paper to a Setlec-style project.

- Abstract: "*While in that context the property of normalisation has attracted the most light, we instead emphasize the importance of **injectivity** properties, showing that they alone are both crucial and sufficient to certify most desirable properties of conversion checkers. **We also explore the certification of a fully untyped conversion checker, with respect to a typed specification**, and show that the story is mostly unchanged, although the exact injectivity properties needed are subtly different.*"
- §1: "*An important takeaway of our work is that, in a sense, **talking about untyped conversion is misleading: we should rather be talking about term-directed typed conversion**. … Yet types are still present in invariants, silently keeping the algorithm on rails.*"
- §1: "*[Injectivity properties] cannot be shown by mere inversion of the conversion derivation, which can go through a long chain of transitivities. **Injectivity shortcuts this**, saying that, despite transitivity, certain congruences are invertible.*"
- §4.3: "*the seemingly innocuous transitivity is actually a source of headaches [Siles & Herbelin], because it means **"real" untyped conversion can relate well-typed terms through ill-typed ones**, which cannot be easily emulated by its typed counterpart.*"
- §5 (Avoiding normalisation): "*Confluence is powerful and scalable, as demonstrated by MetaRocq. **Parallel reduction has been adapted to typed conversion** and η for functions and pairs, although neither work tackle the combination of the two. A different approach is taken by Coquand and Huber, who use a semantics in domains to obtain rich injectivity properties.*"
- Dependency chain (Fig. 1): injectivity of type constructors ⟹ positive soundness; + term-level injectivities + completeness of neutral conversion ⟹ negative soundness; + deep normalisation ⟹ termination.
- On Lean's kernel strategy (§4.4): "*Lean takes an intermediate solution, **re-inferring the type of neutrals on the fly if their untyped comparison fails**.*"

Alternative to confluence entirely: **Abel, Öhman, Vezzosi, "Decidability of Conversion for Type Theory in Type Theory", PACMPL 2(POPL):23, 2018** (Agda, Kripke logical relation, instantiated twice — once for canonicity/injectivity, once for algorithm completeness); **Adjedj, Lennon-Bertrand, Maillard, Pédrot, Pujet, "Martin-Löf à la Coq", CPP 2024**, arXiv:2310.06376 (Coq port + decidability of type checking + executable checker, no impredicativity/induction-recursion/extra axioms).

---

# TOPIC 3 — Set-theoretic models of DTT with universes

## 3(a) How universe LEVELS are interpreted

Every model uses a hierarchy of inaccessibles / Grothendieck universes; **only Carneiro handles universe polymorphism.**

**Werner, "Sets in Types, Types in Sets", TACS 1997** — <https://www.lix.polytechnique.fr/~werner/publis/tacs97.pdf>. §1: "*The number of inaccessible cardinals needed is **exactly the number of universes** of the modelized type theory.*" §3.3: assumes an increasing sequence (κᵢ) of inaccessibles, `A(i) ≜ V_{κᵢ}`, `|Γ ⊢ Typeᵢ|(γ) ≜ A(i)`, `|Γ ⊢ Prop|(γ) ≜ {0,1}`, proofs ↦ 0. §3.2: a set with the universe closure conditions "implies the existence of an inaccessible cardinal" — necessity, not convenience. Theorems 16/20: ZFC_{i−1} ⊢ Con(CIC_i); ZFC + n inaccessibles encodable in CIC_{n+2}+EM+TTDA. **Concrete metalevel level indices only; no level variables, no max/imax, no polymorphism.** Conversion via untyped confluence + subject reduction (Corollary 7) — possible only because Coq lacks definitional proof irrelevance.

**Barras, "Sets in Coq, Coq in Sets", JFR 3(1):29–48, 2010**; habilitation 2012; Coq development <https://github.com/barras/cic-model>. Uses **Grothendieck universes** ("equivalent to inaccessible cardinals in theories where the axiom of choice holds") inside **IZF_R**, formalized in Coq. JFR §4: model of CCω = model of CC + a sequence (uᵢ) with `∗ ∈ u₀`, `uₙ ∈ uₙ₊₁`, `uₙ ⊂ uₙ₊₁`, closed under dependent products; "We require the existence of an infinite sequence of inaccessible cardinals." In code, **one Grothendieck universe per metalevel `nat`**: `ModelECC.v` has `Definition type (n:nat) := cst (ecc n)`. Cumulativity = **set inclusion** (hab. Def 5.14: `Γ ⊢ T ≤ T′ ≜ ∀ρ. Val(T)ρ ⊆ Val(T′)ρ`). **No level variables, no imax.** Uses **Aczel's function encoding** (`cc_lam A f := {(x,y) | x∈A, y∈f(x)}`, `props := P{∅}`) so the model needs no sort determination. Equality judgment is **context-relative (typed)**; JFR: "*in a set theoretical model, functions do not behave like a λ-term outside their intended domain… **This also explains why it is not as easy as expected (see [Miquel–Werner]) to build set theoretical models of type systems which consider type convertibility as an untyped relation.***" Habilitation §5: "*we will not address the problem of showing the equivalence between the judgmental equality presentation and the one where conversion is an untyped relation of terms*" (delegated to Adams/Siles or SN).

**Lee & Werner, LMCS 7(4:05), 2011** (<https://arxiv.org/pdf/1111.0123>) and **Timany & Sozeau, "Consistency of pCuIC", arXiv:1710.03912v3**: both **ZFC + countably many strongly inaccessible cardinals**; `Typeᵢ ↦ V_{κᵢ}`, `Prop ↦ {∅,{∅}}`; **Aczel trace encoding** (`Lam(f) ≜ ⋃_{(x,y)∈f}{x}×y`, `App(f,x) ≜ {y | (x,y)∈f}`) explicitly to fix Werner's counterexample (T–S Example 3.5: `I ≡ λ(P:Type₀). P→P` applied to a true proposition — "*we should have {∅} = {∅}^{∅}… which is not the case*"). Both use **typed judgmental equality** `Γ ⊢ t ≃ t′ : A`; soundness by mutual induction (T–S Thm 4.15), consistency Cor 4.16; cumulativity ⟹ ⊆ (Thm 4.15(4)); inductives via Aczel rule sets. **Universe polymorphism not interpreted** — sorts are concrete `Typeᵢ`; T–S's "universe polymorphic" examples are families of separately instantiated constants (Example 2.12). Both pen-and-paper.

**Carneiro, "The Type Theory of Lean", MSc thesis, CMU, April 16 2019** — <https://github.com/digama0/lean-type-theory>, PDF at release v1.0. **The only model handling `imax` and level variables.**
- **Level syntax** (§2.1, p. 6): `ℓ ::= u | 0 | Sℓ | max(ℓ,ℓ) | imax(ℓ,ℓ)`; 15-rule algorithmic `ℓ ≤ ℓ′ + n` (n∈ℤ) including the variable case-split `ℓ[0/u] ≤ … ∧ ℓ[Su/u] ≤ … ⟹ ℓ ≤ ℓ′+n`.
- **Semantics** (p. 7), verbatim: "*A level takes values in ℕ… ⟦imax(ℓ₁,ℓ₂)⟧ = imax(⟦ℓ₁⟧,⟦ℓ₂⟧) where imax(m,n+1)=max(m,n+1) and imax(m,0)=0. Then a level inequality holds if **for all substitutions v of numerals for the variables**, ⟦ℓ⟧v ≤ ⟦ℓ′⟧v + n.*" Level equality `ℓ ≡ ℓ′` = mutual ≤.
- **Levels are eliminated before the model is built** (§6.1 "Proof splitting", pp. 32–34): fix a valuation `v : Vars → ℕ`; translate to a "proof-split" language where propositional `∀`/`λ`/app and computational `Π`/`Λ`/`·` are syntactically distinct and levels are concrete naturals. The translation is **type-directed** via `lvl`/`sort` functions (Lemma 6.1), which exist **only because of unique typing**. "*Although this type theory is less expressive than the original due to the lack of universe parametricity, it is sufficient to capture situations where the universes have been fixed, in particular in evaluation and in proofs of contradiction, **which can have all universe variables set to zero while preserving the proof***" (p. 34). Cor 6.8 uses "the universe valuation that sets every variable to 0."
- **The model** (§6.2, p. 35): "*Fix an increasing sequence (κₙ) of strong limit cardinals… n-correct if κ₀,…,κₙ₋₁ are all inaccessible… Now let U₀ = {∅,{•}}… and Uₙ₊₁ = V_{κₙ}.*" `⟦∀x:α.β⟧γ = {•} ∩ ⋂ β̄(x)`, `⟦Πx:α.β⟧γ = ∏ β̄(x)`, `⟦λ⟧ = •`; standard ZFC functions (not Aczel encoding — affordable because of unique typing).
- **How many inaccessibles:** per-derivation. Thm 6.7: "*there exists a k such that if the κ sequence is k-correct…*"; "*The proof is constructive for the value of k; it is essentially just the max of all universe numbers that appear in the course of the proof.*" Cor 6.8: "**Lean is consistent if ZFC + {there are n inaccessible cardinals | n ∈ ω} is**"; abstract: "*As Lean supports models of ZFC with n inaccessible cardinals, this is optimal.*"
- **§6.4 Type injectivity:** the plain model conflates distinct types; a "tagged types" layer `Tₙ` (`(Π,A,B)`, `(U,n−1)`, … with decoding ⌊·⌋) restores a semantic analogue of unique typing (Thm 6.9).
- **The two routes, in Carneiro's own words** (§1.2, p. 4): the Miquel–Werner problem "*arises here as well, and the key step in overcoming it is the unique typing property… In [Barras 2010], Barras uses a simple and ingenious trick… Aczel's encoding of functions… This simple property means that **we don't need to determine the sorts of types and elements in the construction, and so we can avoid the dependency on unique typing in the proof of soundness. So if our only goal was proving soundness we could skip section 4 entirely.**"

Lean4Lean's `VLevel` (`Theory/VLevel.lean`) mirrors this exactly: `eval : List Nat → Nat` with `imax`, `Equiv a b ≜ a.eval = b.eval`, `LE ≜ ∀ ls, eval ≤ eval` — level equality = extensional equality under all valuations.

## 3(b) Does anyone verify an executable CHECKER against a set model?

**No — for any dependent type theory.** Mechanized models target declarative/judgmental typing; verified checkers target declarative typing, never a model.

- **Lean4Lean** (arXiv:2403.14064, v2 Dec 2024 / v3 Sep 2025; repo <https://github.com/digama0/lean4lean>): **no set-theoretic model in the formalization** (the `Verify` tree relates `Expr` to `VExpr`/declarative typing only). TYPES 2025 abstract (<https://msp.cis.strath.ac.uk/types2025/abstracts/TYPES2025_paper31.pdf>): "*while there is an intended interpretation within a classical set-theoretical model ([Car19], based on [Wer97]), **the proof of soundness has not been formalized**.*" What is verified is **positive soundness against declarative typing** (v3 §4): "*isDefEqCore… if it is called on well-typed expressions e₁⇝e₁′ and e₂⇝e₂′, and it returns true, then e₁′ ≡ e₂′*". v3 §4.1: "***Currently, only a few functions from the typechecker have been verified**, like inferLambda*" (one real kernel soundness bug found via `looseBVarRange` bit-masking). Termination is fuel-based by design (v2 §3.2.1: "*the Lean type theory is known not to terminate. Coquand and Abel constructed a counterexample…*"). Inductive types are `sorry` at the theory level (`VInductDecl.WF := sorry`).
  **Unique typing downgraded to a conjecture** (§2.4, verbatim): "*The reason Conjecture 2.7 [unique typing] and Conjecture 2.9 [definitional inversion] have been downgraded from theorems in [6] to conjectures here is because **the proof has an error in one of the technical lemmas**… **this stratification does not and cannot respect substitution**; that is, if Γ, x:β ⊢ᵢ e : α and Γ ⊢ⱼ e′ : β, then the proof requires Γ ⊢_{max(i,j)} e[x↦e′] : α but only Γ ⊢_{i+j} e[x↦e′] : α holds. … **The proof of soundness is not impacted because there are alternative routes to construct the model that avoid unique typing (also described in [6]), but these conjectures are necessary in at least some form in order to prove the correctness of the typechecker.**"
  At repo HEAD (pushed 2026-08-29), `Theory/Typing/UniqueTyping.lean` has a ~160-line proof of `IsDefEq.uniq` via `HasTypeStratified`, **but** it imports `Theory/Typing/Injectivity.lean`, whose header reads verbatim `/-! A bunch of important structural theorems which we can't prove :( -/` and which `sorry`s `IsDefEqU.sort_inv`, `IsDefEqU.forallE_inv_stratified`, `forallE_inv`, `sort_forallE_inv`. Unique typing currently stands **conditional on unproved injectivity of type constructors**. *(Source inspection, not build-verified.)*
- **MetaCoq / "Coq Coq Correct!" (POPL 2020)**, <https://sozeau.gitlabpages.inria.fr/www/research/publications/Coq_Coq_Correct-POPL20.pdf>: type inference "*returns a type A **together with a proof term that Σ;Γ ⊢ t : A**. It is thus correct by construction*" — against **declarative PCUIC typing**, not a model. Assumptions verbatim: "*our formalisation **assumes strong normalisation** of the reduction of CIC. We also assume other properties of the metatheory: subject reduction, validity, strengthening, guard condition for inductive types and fixpoints and proof-irrelevance. **This is the only Achilles heel of our formalisation**…*" (the guard is literally `Axiom fix_guard : mfixpoint term → B`). POPL'20 lacks completeness; the **JACM 2025** version (Sozeau, Forster, Lennon-Bertrand, Botsch Nielsen, Tabareau, Winterhalter, *Correct and Complete Type Checking and Certified Erasure for Coq, in Coq*, JACM 72(1), <https://dl.acm.org/doi/10.1145/3706056>) adds it — still modulo the normalization axiom, still no model.
  Carneiro's contrast (Lean4Lean v2 §7): "*Unlike in Lean4Lean, the conversion relation is untyped: there is no mutual induction between typing and definitional equality, which massively simplifies matters. **In Lean this is unfortunately not an option because of the t-proof-irrel rule, which is absent in Coq.**"
- **Barras's cic-model** proves consistency + SN of CC/ECC/CIC-fragments against the model in Coq — but **no executable checker is connected to it**. His 1990s "Coq in Coq" line verified decidability of type checking against *syntactic* metatheory, not the model.
- **Lennon-Bertrand FSCD 2025** assessment of the field (§5): "*Lean4Lean's checker is on par with Lean's kernel, but **only describes its intended type system without relating it to the checker, and develops only minimal meta-theory**… Agda-Core… provide a checker returning typing derivations, thus ensuring positive soundness by construction. **Only MetaRocq develops a comprehensive meta-theory**… backing a certified sound, complete and terminating checker — up to normalisation, which is axiomatised. We encourage them to adopt the 'meta-theory as black box' motto.*"
- **The one genuine precedent is HOL, not DTT:** **Kumar, Arthan, Myreen, Owens, "Self-Formalisation of Higher-Order Logic: Semantics, Soundness, and a Verified Implementation", JAR 56:221–259, 2016**, <https://www.cl.cam.ac.uk/~mom22/jarhol.pdf> — mechanised set-theoretic semantics of HOL + soundness of the HOL Light kernel rules + "*a synthesised implementation of the kernel in CakeML **refines the inference system***". And notably **parametric in the set theory**: "*we improve on Harrison's work by **making our model of HOL parametric on the universe of sets**"*, via `is_set_theory (mem : U → U → bool)` axiomatising Zermelo over a type variable `U`. This is the same architecture as a parametric `SetTheory` interface, but for a vastly simpler, conversion-free logic.

## 3(c) Carneiro's thesis on Lean's defeq — this is your theorem, and it is published

Independently re-verified by me from the PDF.

**Abstract, p. 1, verbatim:**

> "We also show a number of negative results, where the theory is less nice than we would like. In particular, **type checking is undecidable**, and the type checking as implemented by the Lean theorem prover is a **decidable non-transitive underapproximation of the typing judgment. Non-transitivity also leads to lack of subject reduction, and the reduction relation does not satisfy the Church-Rosser property**, so reduction to a normal form does not produce a decision procedure for definitional equality. However, a modified reduction relation allows us to restore the Church-Rosser property at the expense of guaranteed termination, so that unique typing is shown to hold."

**§1.2, p. 4:** "*a combination of subsingleton eliminating inductive types and definitional proof irrelevance breaks the decidability of Lean's type system, making a number of desirable properties fail to hold.*"

**The two relations (§2.2–2.3, pp. 6–7).** "Ideal" `≡` (transitivity, congruence, β, η, proof irrelevance `Γ⊢p:P, Γ⊢h:p, Γ⊢h′:p ⟹ Γ⊢h≡h′`) vs "algorithmic" `⇔` "which will imply α ≡ β and is what is actually checked by Lean". Of `⇔`: "**In this judgment the transitivity rule is notably absent.**" Even `⇔` is *not* untyped — its proof-irrelevance rule has premises `Γ⊢p:P, Γ⊢h:p, Γ⊢h′:p′, Γ⊢p⇔p′`.

**§3.1 Undecidability (pp. 16–17).** Via `acc` and `inv_x : acc x → ∀y. y < x → acc y`, **by proof irrelevance** `a ≡ intro_acc x (inv_x a)`; with `f := rec_acc (λ_.1) (λn g. if P n then g (n+1) (p n) else ())`, "*f 0 a ≡ f 0 (intro_acc 0 (inv₀ a)) ≡ f 1 (inv₀ a 1 (p 0)) ≡ … So **a : acc_> 0 ⊢ f 0 a ≡ () holds if and only if ∀n. P n, and hence ≡ is undecidable**.*" Also: "definitional equality works in all contexts, including inconsistent ones."

**§3.1.1 "Algorithmic equality is not transitive", p. 17, verbatim:**

> "given that algorithmic equality is implemented by Lean, and hence is obviously decidable, they cannot be equal as relations… we can typecheck the various parts of the equality chain to see that **⇔ is not transitive**:
> `f 0 a ⇔ f 0 (intro_acc 0 (inv₀ a)) ⇔ f 1 (inv₀ a 1 (p 0))` but `f 0 a ⇎ f 1 (inv₀ a 1 (p 0))`.
> We can think of the middle step … as a **'creative' step**, where we pick one of the many possible terms of type acc_> 0 which happens to reduce in the right way. But since the expression f 0 a is a normal form, we don't attempt to reduce it, and indeed if we did we would have nontermination problems (since reduction here only makes the term larger). **Note that the fact that we are in an inconsistent context doesn't matter for this: we could have used a : acc_< 1 with the same result.**"

**Second, independent source of non-transitivity — quotients of propositions (same section):**

> "There is another, less known source of non-transitivity: quotients of propositions… `lift_R α f H q ⇔ lift_R α f H (mk_R h) ⇔ f h` but `lift_R α f H q ⇎ f h`."

**§3.1.2 Failure of subject reduction, p. 17, verbatim:** "*While the type system given here actually satisfies subject reduction… this is because we use the ≡ relation in the conversion rule. If we used algorithmic equality instead, to get a variant typing judgment Γ ⊩ e : α closer to what one would expect of the Lean typechecker, we find **failure of subject reduction, directly from failure of transitivity**. If Γ ⊢ α ⇔ β, Γ ⊢ β ⇔ γ, Γ ⊢ α ⇎ γ, and Γ ⊩ e : γ, then: Γ ⊩ id_β e : β … Γ ⊩ id_α (id_β e) : α … But Γ ⊮ id_α e : α because this requires Γ ⊢ α ⇔ γ which is false. Since we obviously have id_β e ▷ e by the β and δ rules, this is a counterexample to subject reduction.*"

**The bridge lemma — Lemma 3.4.(3), p. 18:** "*(3) If Γ ⊢ e : α and Γ ⊢ e′ : α, and Γ ⊢ e ⇔ e′, then Γ ⊢ e ≡ e′. … lemma 3.4.(3) is the main reason we are interested in algorithmic equality, since it is **a thing we can check which implies 'true' well-typedness**.*" **Note the precondition: both sides must already inhabit the same type α.** No "⇔ is an equivalence" theorem is available.

**§4.1 κ-reduction, pp. 19–22:** "*The standard formulation of the Church-Rosser theorem, when applied to the ▷ reduction relation, is not true; under reasonable definitions of reduction, **Lean will not have unique normal forms, because of proof irrelevance**… we will split the definitional equality judgment into two parts: A βδζι-reduction relation (henceforth abbreviated κ reduction), and a relation that does proof irrelevance [≡p].*" Structural facts: the section assumes "*that ⊢ₙ has unique typing, which will prevent the appearance of certain pathologies*"; η fights ι on subsingleton eliminators (`λh:a=a. rec^a_= C e a h` η-reduces to `rec^a_= C e a`, ι-reduces to `λh:a=a. e`), fixed by η-expanding every `rec`/`lift` to full arity ("rec-normal form"); the K⁺ rule carries a **typed side condition**: "*It applies only when intro inv[p,h] is well-typed (**and is the reason why κ needs a context**)*". CR holds only modulo `≡p` — **Theorem 4.7**: "*If Γ ⊢ e : α, and e ▷*κ e₁ and e ▷*κ e₂, then there exists e₁′ and e₂′ such that Γ ⊢ e₁′ ≡p e₂′, and e₁ ▷*κ e₁′ and e₂ ▷*κ e₂′.*" Theorem 4.11 (completeness of κ) and Theorem 4.12 (definitional inversion at level n+1) close the induction.

**§2.6.4, p. 12, "K-like reduction" defined:** "*there is a second reduction rule called 'K-like reduction' used for subsingleton eliminators. It can be thought of as a combination of proof irrelevance to change the major premise into a constructor followed by the iota rule… The foremost example… is known in the literature as axiom K… `rec^a_= C x a h ≡ x`.*"

**§2.8, p. 15, why Coq escapes:** "*Lean supports definitional proof irrelevance, while Coq merely has an axiom that asserts this as a propositional equality. This is a major departure for the theory, and **the reason why the counterexamples in section 3.1 don't work in Coq**.*"

**Does the thesis say "proof irrelevance is not a congruence on untyped terms"?** Not in those words — in his system proof irrelevance is never defined on untyped terms; `≡`, `≡p`, `⇔` all carry contexts and typing premises. Closest: §3.1.1 (non-transitivity of ⇔) and §4.1 ("Lean will not have unique normal forms, because of proof irrelevance").

## 3(d) Published results that untyped proof-irrelevant / K-like conversion breaks confluence, congruence or transitivity

Four distinct, citable results — **not** the same statement, so pick deliberately.

**D1. Untyped K-rule breaks Church–Rosser.** Werner, "On the strength of proof-irrelevant type theories", LMCS 4(3:13), 2008, <https://lmcs.episciences.org/1142/pdf>, §2.4, verbatim:
> "allowing, for any e, the reduction rule (Eq_rec A P a b p e) ▷ p is too permissive, since it **easily breaks the subject reduction property in incoherent contexts**. We therefore put the burden of checking convertibility between a and b on the reduction rule… `(Eq_rec A P a b p e) ▷ p if a =ε b`. When being precise, this means that =εβ and ▷ are actually **two mutual inductive definitions**. An alternative would be the non-linear rule `(Eq_rec A P a a p e) ▷ p` but **this allows an encoding of Klop's counter-example and thus breaks the Church-Rosser property (for untyped terms)**."

The cleanest published citation for "K-like reduction on untyped terms is non-confluent" — exactly the Lean kernel's K-like rule. Werner's design response: syntactic relevance **tags** on variables (`x^∗ ▷ε ε`, Def 2.1) with tag-preservation side conditions on β (Def 2.2: "*Without them (λx^⋄:Prop.x^⋄ Prop) can reduce either to ε or to Prop which would falsify the Church-Rosser property*").

**D2. Normalization fails outright, in Lean, on a closed term.** Abel & Coquand, "Failure of normalization in impredicative type theory with proof-irrelevant propositional equality", LMCS 16(2:14), 2020, <https://lmcs.episciences.org/6606/pdf>. Abstract: "*It refutes Werner's normalization conjecture published in LMCS [Wer08, Conjecture 3.14].*" Mechanism: `cast : Π A B : Prop. A =Prop B → A → B` with `cast A A e x ▷ x` "*that **does not inspect the equality proof e** but only checks whether the endpoints are (definitionally) equal*". First counterexample (open, under `h : all props equal`): `Ω h ▷⁺ Ω h`; "*normalization that proceeds under λ-abstraction can diverge. This means that **equality of open terms cannot be decided just by normalization**.*" Second uses only Lean's standard axiom `propext`, with runnable Lean 3.4.2 code (`def Omega : True := delta omega`): "***Note that term Omega is closed with respect the standard axioms of Lean, and does not even have a weak head normal form.***" Also: "*As both [equality and Acc] may be eliminated into computational universes, **decidability of definitional equality is lost, as demonstrated by Carneiro**… As a consequence, typing is not decidable.*" Acknowledgment: "*We thank Mario Carneiro for contributing the original Lean implementation of the first counterexample.*"

**D3. Lean's partial proof irrelevance breaks subject reduction — with runnable code.** Gilbert, Cockx, Sozeau, Tabareau, "Definitional Proof-Irrelevance without K", PACMPL 3(POPL):3, 2019, <https://jesper.sikanda.be/files/definitional-proof-irrelevance-without-K.pdf>.
- §1: the accessibility predicate "*satisfies the singleton elimination criterion but implementing definitional proof irrelevance for it **leads to an undecidable conversion and thus an undecidable type checker**.*"
- On Lean, verbatim: "*An alternative approach is to do as in Lean, where they do have proof irrelevance with singleton elimination, but they only implement a **partial version of proof irrelevance** for recursive inductive types satisfying the singleton elimination, which is **restricted to closed terms**. But this partial implementation of the conversion algorithm **breaks in particular subject reduction**… (see a concrete example in Appendix A).*" (fn. 2: github.com/leanprover/lean/issues/654)
- **Appendix A "LEAN SUBJECT REDUCTION FAILURE"**: runnable Lean 3 code where `fix_F_eq1`, `fix_F_eq2` hold by `eq.refl _`, `fix_F_eq3` (their composition) holds by `eq.trans`, but `fix_F_eq4` — the same statement, by `eq.refl _` — fails. A direct executable witness of **non-transitivity of the kernel's conversion**.
- §4.5: with proof irrelevance, "***conversion can not be defined independently from typing**, and the standard technique to prove decidability of type checking developed by Andreas Abel and others based on algorithmic equality and logical relations **does not apply**.*" Their fix (relevance marks on binders) rests on **uniqueness of typing** (Prop 4.4) and forbids implicit sProp→Type cumulativity.

**D4. The model-side obstruction to untyped conversion.** Miquel & Werner, "The not so simple proof-irrelevant model of CC", TYPES 2002, <https://www.lix.polytechnique.fr/Labo/Benjamin.Werner/publis/cc.pdf>, §2.4 "The unattainable soundness": every case of model soundness goes through except the conversion rule; the needed lemma is "*Conjecture 1 (Soundness of β-reduction)… **Unfortunately, the conjecture 1 is wrong**"*, with counterexample `t = (λx:T. x) ∗` for `T = ΠX:∗.X→X` (`⟦T⟧={•}`): `⟦t⟧ = •` but `t →β ∗` with a different denotation. Restricting to well-typed terms is circular: "*in order to prove this conjecture, we need the soundness property… that needs this conjecture to be proved!*" Encoding-independently: "*the problem… is due to the fact that **the identification of all proof-terms requires to forget the domain of the corresponding functions**.*" Fixes: sorted syntax (variables tagged by sort; correctness from uniqueness of types) or judgmental equality (§5.2, citing Streicher), where "*the difficulty is then shifted to the (syntactic) subject-reduction property*."

**Not found:** a paper stating as a named theorem, in abstract form, "the untyped relation generated by β + {h ≡ h′ for h,h′ proofs} is not transitive / not a congruence." The literature states it in the four concrete forms above. For "untyped K/proof-irrelevant reduction is non-confluent" cite **D1**; for "Lean's algorithmic defeq is non-transitive" cite **Carneiro §3.1.1**; for "Lean kernel breaks SR" cite **Carneiro §3.1.2 + Gilbert et al. Appendix A**; for "non-normalizing closed Lean term" cite **D2**.

## 3(e) Live Lean issues (engineering artifacts complementary to the papers)

Cited as `[2]` in Lennon-Bertrand FSCD 2025:

- **leanprover/lean4#2258, "DefEq transitivity failures for unit-like eta"** (arthur-adjedj, 2023-06-06, open, P-low), <https://github.com/leanprover/lean4/issues/2258>: `(p q : α → Unit) : p = q` fails though `p = λ _ => ()` and `λ _ => () = q` each succeed; likewise for `structure Foo where foo : Unit` and `structure Bar : Type where bar : True`. Root cause: `isDefEqUnitLike` criteria too restrictive.
- **leanprover/lean4#12520, "DefEq transitivity failure for function eta"** (nomeata, 2026-02-17, open), <https://github.com/leanprover/lean4/issues/12520>: "*The type-checker applies function eta only when one side of the equation is a manifest lambda. But there are other forms where eta-expanding would be productive, e.g. partially applied `Eq.rec`. **This leads to a intransitivity of defeq checking**.*" With a three-line `Eq.rec` example; "*similar in spirit to #2258*".
- **leanprover/lean4#3213, "Eta-expansion of `Prop`-structures"** (arthur-adjedj, 2024-01-23), <https://github.com/leanprover/lean4/issues/3213>: during ι-reduction, `Prop`-valued structures are not η-expanded; "***This, among other things, break both the transitivity and congruence of definitional equality.***" Example: `And.rec f ⟨x.1,x.2⟩ = f x.1 x.2` holds by `rfl`, but `And.rec f ⟨x.1,x.2⟩ = And.rec f x` fails.

The Lean kernel's proof-irrelevance check **re-infers types** (`isDefEqProofIrrel`: `inferType` both sides, `isProp`, then `isDefEq` of the two types) — confirmed in lean4lean source at HEAD.

---

# Practical takeaways

- **NEED A has a named theorem: RuS / the Square Brackets Lemma.** Lemma 7 of Endrullis–de Vrijer is the weak-head dichotomy verbatim; Corollary 1 covers capture (telescopes); the whole proof is three lemmas over the four-clause inductive relation `⤳` of Lemma 9 — a small, self-contained Lean development. Nobody has mechanized it.
- **You do not need residuals or Lévy labels.** Every mechanized standardization since McKinna–Pollack deliberately avoids them; the Xi/Kashima inductive `⇝st` relation is the mechanization-friendly route (Guidi, Copes et al., Abel's Abella, ITP 2025).
- **Cheaper alternative to porting RuS:** Accattoli–Lancelot's light-genericity proof gets the same conclusion using only forward simulation (plus its contrapositive on divergence) and an induction over **core** normal forms. That's "confluence + forward simulation, then analyse the join" in its cheapest form.
- **Two caveats for a kernel:** (1) **βη does not satisfy head factorization** (Factorize Factorization, Example 4.6) — a standardization-based structuring of traces must be re-earned per rule via their linear-swap test (Prop. 4.5), not assumed; (2) RuS is stated for pure β, and residual theory generally wants orthogonality — Lean's rules (proof irrelevance, K-like, η) are not orthogonal. van Oostrom's "Invert" (Finite Family Developments, RTA'97, LNCS 1232) is the pattern-generalized SqBL and is the right next thing to look at.
- **The Aczel-encoding escape from unique typing is now load-bearing, not an optimization.** Carneiro §1.2 says soundness can skip §4 entirely with Barras's encoding; Lean4Lean has since downgraded unique typing to a conjecture. Any model-construction dependency on unique typing is worth removing.
- **Nobody has connected an executable DTT checker to a set model.** The only precedent for the full chain — and it uses exactly the parametric-`SetTheory` architecture — is Kumar–Arthan–Myreen–Owens for HOL Light/Candle.
- **Your refutation is close to, but not identical with, published results.** The literature does not state "proof irrelevance is not a congruence on untyped terms" abstractly. It states four concrete things (D1–D4 above). If your refutation is genuinely about *untyped* proof-irrelevant conversion as a congruence, it may be a novel abstract packaging of Werner §2.4 + Carneiro §4.1 — worth checking that framing carefully.

---

# VERIFIED FACTS

1. RuS (Endrullis–de Vrijer RTA 2008; van Daalen 1980) states exactly the forward dichotomy for `M[x:=L] ↠ N`: Lemma 6 (single), Theorem 13 (multiple), Corollary 1 (context filling with capture), Theorem 23 (prefix independent of substitution). Barendregt Exercise 15.4.8; *Lambda Calculus Satellite* §1.3.
2. Square Brackets Lemma (Lemma 7) gives exactly the weak-head-form case split.
3. The RuS proof reduces to: inductive relation `⤳` (Lemma 9, four clauses), substitution stability (Lemma 11), and commutation `⤳ · ↠ ⊆ ↠ · ⤳` (Lemma 12), whose three cases are prefix / below-prefix / interface, the last resolved by refining the prefix context.
4. Lévy's three creation cases I/II/III are enumerated verbatim in Bonelli–Barenbaum (EPTCS 15, 2010, doi 10.4204/EPTCS.15.2); type III is the substituted-λ-meets-argument case; superdevelopments cover only I and II; weak reduction adds a type IV.
5. Backward simulation *does* hold when substituted terms are inert/accumulators: Accattoli–Guerrieri, Lemma 42, arXiv:1609.00322; inert terms "cannot create a redex"; Grégoire–Leroy call them accumulators.
6. Mechanized residual theory exists in Coq (Huet, JFP 1994: Prism Theorem, Lévy's Cube Lemma) and Isabelle/AFP (Stark 2022: RTS + finite developments + standardization + leftmost reduction). Standardization mechanized in Abella (Abel 2009; Lancelot et al. ITP 2025), Matita (Guidi 2012), Agda (Copes et al.), LEGO (McKinna–Pollack), Isabelle (Gheri–Popescu). A Lean 4 confluence/SN framework exists (arXiv:2512.09280, 10,367 lines / 497 theorems / zero axioms) but has no residuals or standardization.
7. Head factorization/normalization gives the head-steps-first structuring (ITP 2025 Thm 7, Thm 8, Cor. 12). **βη breaks head and leftmost factorization** (Factorize Factorization §3 and Example 4.6, with explicit counterexample); their Prop. 4.5 gives a modular per-rule test.
8. MetaCoq uses confluence (Takahashi triangle on context/term pairs) to get "conversion = joinability up to α-cumulativity" and thence Π-injectivity, rather than inverting steps; confluence is what makes the directed relation transitive.
9. Accattoli–Lancelot prove light-genericity-as-substitution without inverting image steps: contrapositive forward simulation, run core to hnf, push forward, induct on core normal forms.
10. Isabelle `HOL-Proofs-Lambda` proves `eta_postponement`.
11. Lennon-Bertrand (FSCD 2025) certifies an untyped conversion checker against a *typed* spec; injectivity is the load-bearing property; transitivity of untyped conversion is a known source of trouble (relates well-typed terms through ill-typed ones); Lean re-infers types for neutrals on failure.
12. Universe levels in set models: `Typeᵢ ↦ V_{κᵢ}` (or Grothendieck universe `ecc i`), one inaccessible per level, `Prop ↦ {∅,{•}}`, cumulativity = ⊆; Werner shows inaccessibles necessary. Werner / Lee–Werner / Timany–Sozeau / Barras: **concrete metalevel indices only, no level variables or imax**; universe polymorphism absent or handled by duplication.
13. Carneiro 2019 is the **only** model interpreting `imax` and level variables: valuation semantics `⟦·⟧v : Vars→ℕ`, `≤`/`≡` = truth under all valuations; the model is built **after** fixing a valuation and type-directedly splitting Prop/Type (needs unique typing via `lvl`/`sort`; avoidable via the Aczel encoding). Consistency relative to ZFC + {n inaccessibles | n<ω}, per-derivation "k-correct" bound, claimed optimal. Lean4Lean's `VLevel` mirrors the level semantics exactly.
14. Carneiro §3.1 (defeq undecidable), §3.1.1 (`⇔` non-transitive; two independent sources: `acc` subsingleton elimination and quotients of propositions; inconsistent context inessential), §3.1.2 (subject reduction fails, directly from non-transitivity), §4.1 (Church–Rosser fails; recovered only for typed context-carrying κ-reduction modulo typed `≡p`, with a typed side condition on K⁺, assuming unique typing at the previous stratification level), Lemma 3.4.(3) (`⇔ ⟹ ≡` only when both sides already share a type). §2.8: the counterexamples don't work in Coq.
15. Lean4Lean downgraded unique typing and definitional inversion from theorems to conjectures ("the stratification does not and cannot respect substitution"); soundness unaffected via the Barras/Aczel route; conjectures still "necessary in at least some form" for typechecker correctness. Repo HEAD proves `IsDefEq.uniq` but rests on sorry-ed injectivity lemmas.
16. Werner LMCS 2008 §2.4: the non-linear untyped K rule "allows an encoding of Klop's counter-example and thus breaks the Church-Rosser property (for untyped terms)". Abel–Coquand LMCS 2020: a **closed** Lean term (`propext` only) with no weak head normal form; refutes Werner's Conjecture 3.14. Gilbert et al. POPL 2019 Appendix A: runnable Lean subject-reduction failure; §4.5: conversion cannot be defined independently from typing.
17. Miquel–Werner 2002: naive proof-irrelevant model is unsound for untyped β on ill-typed terms; restriction to well-typed terms is circular with soundness; root cause is forgetting function domains. Barras (JFR 2010) restates this as why untyped-conversion type systems are hard to model set-theoretically.
18. No executable DTT checker has ever been verified against a set-theoretic model: Lean4Lean = declarative spec only, few functions verified, no formalized model; MetaCoq = sound+complete checker vs declarative typing with normalization/guard/SR axiomatized; Barras = formalized model, no checker. The only kernel verified against mechanized set-theoretic semantics is **HOL Light/Candle** (Kumar et al. JAR 56:221–259, 2016), with a **parametric** set theory (`is_set_theory mem` over a type variable `U`).
19. Live Lean issues #2258, #12520, #3213 document concrete defeq transitivity/congruence failures in the shipped kernel; #3213 explicitly says the problem "break[s] both the transitivity and congruence of definitional equality".

# COULD NOT VERIFY

- **The full appendix-level detail of Endrullis–de Vrijer's Theorem 13** (multiple substitution). I read the statement and the proofs of Lemmas 9–12 and Thm 13, but not every supporting detail.
- **No mechanization of RuS or the Square Brackets Lemma in any proof assistant.** Targeted searches turned up nothing — absence of evidence, not proof of absence.
- **Whether RuS survives δ/ι/projection/η/proof-irrelevance.** RuS is proved for pure β. van Oostrom's "Invert" (Finite Family Developments, RTA'97, LNCS 1232) is stated for arbitrary patterns in orthogonal higher-order systems per the RuS paper's §2 remark; I could not obtain van Oostrom's PDF to check the precise statement or its orthogonality hypotheses.
- **Aczel, "On relating type theories and set theories" (TYPES '98, LNCS 1657, pp. 1–18)** — primary PDF unobtainable (Manchester links dead, Wayback returns HTML, Springer authwalled). The "Aczel trace encoding" definition is verified only *indirectly*, but identically, from four fetched sources (Barras JFR §3.2, Lee–Werner Def 3.2/Lemma 3.3, Timany–Sozeau Def 3.6/Lemma 3.8, Carneiro §1.2).
- **MetaCoq JACM 2025 full text** — open mirrors returned HTML; the sound+complete claim is from the publisher page and abstract, not the PDF body.
- **Barras's habilitation** — read from a Wayback snapshot (2025-02-16) because the live LSV URL 403s; text complete and consistent but not the canonical copy.
- **Lean4Lean's `IsDefEq.uniq` completeness beyond the visible sorries** — source inspection only, not build-verified; the repo is ahead of the published paper.
- **The GitHub repo URL for the Lean 4 metatheory framework (arXiv:2512.09280)** — a page summarizer reported `github.com/arthuraa/metatheory`, which looks like a mis-attribution. Title, authors, abstract, and stats are verified via the arXiv API; the repo URL is not.
- **A paper stating, as a named abstract theorem, that untyped β + proof-irrelevance is not transitive / not a congruence** — does not appear to exist; only the four concrete forms D1–D4.
- **Gilbert et al. page numbers** are from the author-version PDF; section/appendix references are stable.