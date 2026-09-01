# Report: untyped conversion vs. typed specifications in verified kernels

## TOPIC 1 — MetaCoq / MetaRocq / PCUIC

Sources actually read:
- **Sozeau, Boulier, Forster, Tabareau, Winterhalter, "Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq", POPL 2020** — <https://sozeau.gitlabpages.inria.fr/www/research/publications/Coq_Coq_Correct-POPL20.pdf> (read in full, text-extracted)
- **Sozeau, "Touring the MetaCoq Project" (invited paper, LFMTP 2021), arXiv:2107.07670** — <https://arxiv.org/pdf/2107.07670> (read)
- **Lennon-Bertrand, "What does it take to certify a conversion checker?", FSCD 2025, extended version arXiv:2502.15500v3** — <https://arxiv.org/pdf/2502.15500> (read in full). This is the paper that actually answers your questions; your guessed "Winterhalter ITP 2023" paper does not appear to exist (see "could not verify" below).
- **MetaRocq README** — <https://github.com/MetaRocq/metarocq> (fetched, summary only)
- JACM 2025 successor: **"Correct and Complete Type Checking and Certified Erasure for Coq, in Coq", J. ACM 72(1), Art. 8** — <https://dl.acm.org/doi/10.1145/3706056>. **I could not fetch the full text** (ACM 403, HAL blocked by Anubis); claims about it below are secondhand and flagged.

### (a) Is PCUIC's conversion typed or untyped, and how does it relate to typing?

**Untyped, on raw terms.** Explicitly, from *Touring the MetaCoq Project* §2.2.1 ("Conversion, Cumulativity"):

> "PCUIC is presented in the style of Pure Type Systems, where this conversion relation is **untyped and can be defined independently on raw terms** as the reflexive, symmetric and transitive closure of one-step reduction."

Two refinements from the same section and from *Coq Coq Correct!* §2.2:
- It is a **cumulativity preorder**, not an equivalence: `A ≤ B` holds when `A ↝* A'`, `B ↝* B'`, and `A' ≤ B'` by `leq_term` (α-equivalence parameterised by a relation on universes). Conversion `≡` is cumulativity in both directions (*Coq Coq Correct!* §2.2, p. 8:5).
- Typing is connected to it only through `type_Cumul` (the conversion rule), shown verbatim in *Coq Coq Correct!* Fig. 2: `Σ;Γ ⊢ t : A → (isWfArity … + {s & Σ;Γ ⊢ B : tSort s}) → Σ;Γ ⊢ A ≤ B → Σ;Γ ⊢ t : B`.

Because conversion is untyped and defined independently, **there is no mutual induction between typing and conversion** in PCUIC. That is the single biggest structural difference from Lean's spec (see Topic 2c).

**Subject reduction enters as a theorem, not a definition.** *Touring* §3.2.2: they first prove context conversion/cumulativity and **injectivity of Π-types** (`Πx:A.B ≡ Πx:A'.B' → A ≡ A' ∧ B ≡ B'`), and injectivity of inductive applications up to universe cumulativity; type preservation in the application case follows. Caveat, same section: subject reduction is *parameterised* — it holds only for derivations with no dependent case analysis on co-inductive types, because Coq's theory is broken there. In *Coq Coq Correct!* (2020) §2.3.3 subject reduction, validity and principality were still listed as **work in progress / assumed** (footnote 3 on p. 8:3: "The proofs of subject reduction, validity and strengthening are in progress"); the MetaRocq README now lists subject reduction (excluding case/cofix) as proven.

### (b) Structure of the conversion-algorithm correctness proof; is well-typedness needed?

**Yes, and more strongly than you might expect: well-typedness is needed to even *define* the algorithm.** MetaCoq does **not** use fuel. From *Coq Coq Correct!* §3.1–3.2:

- They define a well-founded order `R Γ` on (term, stack) pairs as a *dependent* lexicographic product of co-reduction `cored` and a position order `positionR` (Fig. 8, p. 8:15).
- `Corollary R_Acc : ∀ Γ t, wf Σ → wellformed Σ Γ (zip t) → Acc (R Γ) t.` (§3.1, p. 8:16). Accessibility is derived **from the strong-normalisation axiom, which is stated only for well-typed terms**.
- `reduce_stack Γ t p (h : wellformed Σ Γ (zip (t,p))) : { t' | Req Σ Γ t' (t,p) }` — the well-formedness proof is a *function argument* (§3.2, p. 8:16).
- The conversion checker is likewise defined "by induction on accessibility of `R`" with "an order … even more involved than the one used for reduction: … a dependent lexicographical order modulo syntactic equality of terms up to cumulativity of universes" (§3.4, p. 8:18).

The correctness style is **correct-by-construction via subset types**, not a separate soundness theorem: `infer Γ (HΓ : ‖wf_local Σ Γ‖) t : typing_result ({A & ‖Σ;Γ ⊢ t : A‖})` (Fig. 10, §3.5). *Touring* §5 states this crisply:

> "the main difficulty in the development of the conversion algorithm is that its **termination and correctness are intertwined**, so it is developed as a dependently-typed program that **takes well-typed terms as arguments** (ensuring termination of recursive calls assuming SN) and returns a proof of their convertibility (or non-convertibility). In other words it is proven sound and complete by construction."

So: **soundness of `convert_leq` is stated only for well-typed (well-formed) inputs** — the type of the function makes ill-typed inputs unrepresentable. POPL 2020 §3.5 ends: "we have **not proven completeness of type inference**" (that is what the JACM 2025 version adds; the lean4lean paper §8 corroborates: "MetaRocq [15,25] has a proof of completeness", and the MetaRocq README says the Safe Checker is "correct and complete w.r.t. the PCUIC specification" — I could not verify the completeness statement in the JACM text itself).

**Axioms.** *Coq Coq Correct!* §2.3.4: `Conjecture normalisation : ∀ Γ t, welltyped Σ Γ t → Acc (cored (fst Σ) Γ) t.` Plus the guard/positivity oracles (Fig. 5: `Axiom fix_guard`, `Axiom fix_guard_red1`, `Axiom ind_guard`), which they say (§2.3.1) they "consider … together with the axiom of strong normalisation … altogether as one axiom". *Touring* §5 says SN "is the only axiom used in the development" and §6.1 says the SN assumption "hence includes an assumption of correctness of the guard checkers".

### (c) Do they need a backward simulation "reduction of a substituted term ⇒ reduction of the original"?

**No — and the structural choice that lets them avoid it is precisely that conversion is untyped and defined by reduction on raw terms.** Everything they need about substitution goes *forward*:

- *Coq Coq Correct!* §2.3.1–2.3.2 proves the forward direction only: `Lemma substitution_pred1` and **Theorem 2.1 (Parallel substitution)**, "the stability by substitution of parallel reduction". They work in a σ-calculus (Autosubst-style) representation, noting the equational theory is "rich, clean and decidable" compared to "the tricky lifting and substitution lemmas of 'traditional' de Bruijn representations" (§2.3.1).
- All *inversions* go through **confluence**, not through simulation. §2.3.2 (Tait–Martin-Löf / Takahashi method): **Theorem 2.2 (Triangle property)** `Γ,t ⇛ ρ(Γ),ρ(t)`, giving **Corollary 2.2.1 (Confluence of Parallel Reduction)**, hence confluence of one-step reduction. *Touring* §3.2.3 states the payoff directly: "**To support inversion lemmas such as Π-type injectivity, we need to show that reduction is confluent.** From this proof, it follows that the abstract, undirected conversion relation `T ≡ U` is equivalent to reduction of the two sides to terms `T'` and `U'` that are in the syntactic α-cumulativity relation."

That last sentence is the crux for your problem: in an untyped-conversion setting, **confluence turns "convertible" into "have a common reduct up to α-cumulativity"**, and injectivity/no-confusion then falls out by inspecting the syntactic relation on the reducts. You never have to reason backwards from a substituted term's reduction to the original's, because you never need a simulation at all — you need a *joinability* statement, which confluence provides in the forward direction.

Two caveats they hit, both worth knowing:
- **Let-bindings break naive context conversion.** §2.3.2: "Due to the action at a distance nature of let-in definiens reduction, we cannot get full context conversion from the substitution lemma. We prove only after confluence that for two [convertible contexts] …". They then define reduction of contexts and derive a confluence lemma for contexts.
- Substituting into contexts with let-ins requires "well-typed substitutions … [that] coherently preserve the [let] definitions" (§2.3.1).

### (d) Role of confluence + standardisation/postponement

- **Confluence is load-bearing and does the job that a logical relation does elsewhere.** It gives: equivalence of undirected conversion with joinability (→ transitivity is free, since `≡` is *defined* as a closure); Π-injectivity and inductive-application injectivity; hence subject reduction (*Touring* §3.2.2–3.2.3). Method: parallel reduction + Takahashi's optimal reduct ρ + triangle property, not the diamond lemma directly (*Coq Coq Correct!* §2.3.2).
- **Standardisation is essentially absent from MetaCoq.** I found no standardisation/postponement result in either MetaCoq document. Lennon-Bertrand FSCD 2025 §5 attributes standardisation to Abel & Altenkirch instead: "They also put forward confluence, injectivity of type constructors, and **standardisation, which gives a form of completeness of weak-head reduction: if a term is convertible to a weak-head normal form, it (weak-head) reduces to a weak-head normal form with the same shape.** This also appeared naturally in our formalisation, although less prominently than injectivity." **That statement is very likely the exact shape of the lemma you want for "sort coherence"** — see the synthesis section.
- **Transitivity** is *not* proved for MetaCoq's conversion — it is definitionally a transitive closure. This is a real asymmetry with Lean.

### Bonus: the FSCD 2025 paper is the direct answer to your framing

Lennon-Bertrand certifies **an untyped conversion checker with η, against a typed specification**, for MLTT with Π, Σ, ℕ, ⊥, Id, one universe (formalisation: <https://github.com/CoqHott/logrel-coq/tree/fscd25>). Key content:

- **Thesis (§1, §4):** "the specification remains typed: specifying η-laws in an untyped way is perilous, although their implementation is reasonable". And: "although no type is visible in the definition of untyped conversion, **the name 'untyped' is misleading**. We still aim to decide the same typed relation, but have merely remarked that we can arrange the algorithm in a way that makes type information superfluous. **Yet types are still present in invariants, silently keeping the algorithm on rails. Untyped conversion may thus be more aptly characterised as term-directed typed conversion.**" (§4, p. 10)
- **Preconditions are explicit and are exactly well-typedness** (Fig. 6, p. 10). E.g. for the raw untyped judgment `t ≅ t'` the precondition is `∃Γ T. Γ ⊢ t:T ∧ Γ ⊢ t':T`, postcondition `Γ ⊢ t ≅ t':T`. For the reduced judgments there is the extra precondition that inputs are weak-head normal forms.
- **Dependency table (Fig. 1, p. 3)**, which is the single most useful artefact for you:
  | | positive soundness | negative soundness (typed) | negative soundness (untyped) | termination |
  |---|---|---|---|---|
  | injectivity of type constructors | ✔ | ✔ | ✔ | ✔ |
  | term-level injectivities | | ✔ | ✔ | |
  | normalisation | | | | ✔ |
- **Property 1 (Injectivity and no-confusion of type constructors)** and **Corollary 3 (Types classify normal forms)**: "consider `t` a normal form. If `Γ ⊢ t : Π x:A.B`, then `isFun t`. If `Γ ⊢ t : ℕ`, then `isNat t`. If `Γ ⊢ t : U`, then `isTy t`. If `Γ ⊢ t : T` and `T` is neutral, then `t` is neutral." **This is your "sort coherence", and it is derived from injectivity + no-confusion, not from any simulation property.** Corollary 2 (Preservation) — `Γ ⊢ A ∧ A ↝* A' ⇒ Γ ⊢ A ≅ A'` — also follows from Property 1 alone, without normalisation.
- **Positive soundness needs no normalisation** (Props 13–14), and is proved by "local preservation lemmas" — one per inductive rule, saying the rule preserves the invariants — assembled by metaprogramming into a "bundled induction principle" that threads invariants through as extra hypotheses in each step (§4.1, p. 11). This is a concrete proof-engineering recipe you could copy.
- **Untyped is strictly harder for negative soundness:** typed conversion only needs Property 9 (completeness of neutral comparison **at positive types**); untyped needs Property 7 (**at all types**) (Prop 15 vs Prop 20, §4.1–4.2).
- **Strengthening, not backward simulation, is the substitution-flavoured lemma they need.** Prop 22 (typed ⇒ untyped) ends: "The extra induction hypothesis for neutrals tells us that `n y ∼ n' y`, or more precisely in de Bruijn syntax, that `n[↑] y ∼ n'[↑] y` … We can easily invert this to `n[↑] ∼ n'[↑]`, and conclude by an auxiliary lemma that **untyped conversion admits strengthening**." And: "while this is readily proven by induction for **algorithmic** judgments, it is generally difficult to prove for **declarative** systems! Admitting easy proofs of strengthening is a major advantage of algorithmic presentations."
- **Proof irrelevance / SProp (§4.4):** "any two proofs are definitionally equal … This is very similar to definitional unit, and of course comes with **similar threat to completeness of neutral comparison**." Their reported implementation strategies: Agda extends its type-directed conversion; **Rocq stays purely term-directed by carrying universe information** (cheap, because SProp is closed under the relevant formers, so `merely maintaining information about the universe is much cheaper` than recomputing types); **Lean "re-infers the type of neutrals on the fly if their untyped comparison fails"**, plus a dedicated (currently incomplete) "unit-like" criterion. The paper does **not** prove or disprove that proof irrelevance is a congruence on untyped terms — it treats it as an open extension.
- **Untyped ⇒ typed needs normalisation** (Prop 24), with a nice counterexample sketch: for `x : B` with `B ≅ ℕ → B`, the untyped algorithm terminates immediately while the typed one "spin[s] in never ending η-expansions".

---

## TOPIC 2 — lean4lean (Mario Carneiro)

Sources actually read:
- **Carneiro, "Lean4Lean: Verifying a Typechecker for Lean, in Lean", arXiv:2403.14064v3 (14 Sep 2025)** — <https://arxiv.org/pdf/2403.14064> (read in full)
- **Repository <https://github.com/digama0/lean4lean>**, cloned at commit `8223d223ed98661882e95d9d6a7126df7097cd76`, dated **2026-08-29**, message "feat: close the substitution sorries with the picked substDF". I inspected the source directly.

### (a) Soundness target

**A type-theory spec: the `VExpr` typing judgment, not a semantic model.** §2.1: `VExpr` is "a minimalistic version of the type actually used by the kernel …, to ease the burden of proving theoretical properties" (bvar/sort/const/app/lam/forallE only). Footnote 7 explicitly contrasts with MetaRocq, which "uses the same type for proving metatheory and for writing metaprograms".

§2.2: **there is exactly one judgment**, `Γ ⊢_{E,n} e ≡ e' : α` (formalised as `VEnv.IsDefEq`), with `Γ ⊢ e : α ≜ Γ ⊢ e ≡ e : α` and `Γ ⊢ e₁ ≡ e₂ ≜ ∃α. Γ ⊢ e₁ ≡ e₂ : α`. Rules (Fig. 1): t-bvar, t-symm, t-trans, t-sort, t-const, t-lam, t-all, t-app, t-conv, t-beta, t-eta, **t-proof-irrel**, **t-extra**. The paper notes this differs from Carneiro's MSc thesis [6], which had two mutually inductive judgments; "we conjecture the two formulations to be equivalent, but this version seems to be easier to prove basic structural properties about", and "Lean does not have good support for mutual inductive predicates".

`t-extra` (`u.(e ≡ e' : α) ∈ E`) is the generic hook by which **inductive iota rules and quotient computation are added as environment-level definitional equalities**, so the core theory has no inductive-specific machinery (§5, §6). §6 notes the payoff: "we do not need a complex guard checker, something which MetaRocq currently axiomatizes".

The paper's target for the *checker* is `TrExpr`: `env; Us; Δ ⊢ e ⤳ e'` relating kernel `Expr` (locally nameless, with fvar/letE/lit/mdata/proj) to spec `VExpr` (pure de Bruijn), via `VLCtx = List (Option FVarId × VLocalDecl)` (§3.1). Note: `letE` is modelled by *expanding* it (`e2[x ↦ e1]`); `proj` desugaring "must be type-aware, and is only well-defined up to definitional equality"; `Nat` literals are unfolded to unary `Nat.succ` towers.

Semantic soundness (relative consistency w.r.t. large cardinals, from the MSc thesis) is explicitly **future work** (§9).

### (b) Proved vs. conjectured/assumed

Proved in the paper (§2.3): Lemma 2.1 (closedness, weakening, level instantiation `instL`, substitution `instN`); Lemma 2.2 `defeqDF_l`; Lemma 2.3 `HasType.forallE_inv`; Lemma 2.4 `HasType.sort_inv`; **Theorem 2.5 `IsDefEq.isType`** (validity); Lemma 2.6 `instDF`.

**Conjectured in the paper (§2.4)** — and this is the heart of the matter:
- **Conjecture 2.7 (`IsDefEq.uniq`, unique typing)**: `Γ ⊢ e:α ∧ Γ ⊢ e:β ⇒ ∃u. Γ ⊢ α ≡ β : Sort u`.
- **Conjecture 2.9 (Definitional inversion)**: `sort_inv` (`Γ ⊢ U_ℓ ≡ U_ℓ' ⇒ ℓ ≡ ℓ'`), `forallE_inv` (Π-injectivity), `sort_forallE_inv` (no-confusion `Γ ⊬ U_ℓ ≡ Πx:α.β`). **This is exactly your "sort coherence".**
- **Conjecture 2.10 (Strengthening)**, with consequences `IsDefEq.skips`, `weakN_iff`, `OnCtx.weakN_inv`.

Crucially, §2.4 explains *why* they were downgraded from theorems in the MSc thesis to conjectures — and it is a substitution/stratification failure that will resonate with you:

> "the proof has an error in one of the technical lemmas … the proof constructs a stratification `⊢ᵢ` of the typing judgment in order to break the mutual induction between typing and definitional equality, but **this stratification does not and cannot respect substitution**; that is, if `Γ, x:β ⊢ᵢ e : α` and `Γ ⊢ⱼ e' : β`, then the proof requires `Γ ⊢^{max(i,j)} e[x↦e'] : α` but only `Γ ⊢^{i+j} e[x↦e'] : α` holds."

He adds: "The proof of soundness is not impacted because there are alternative routes to construct the model that avoid unique typing …, **but these conjectures are necessary in at least some form in order to prove the correctness of the typechecker**", and cites Lennon-Bertrand's FSCD paper as mapping "the landscape of proof approaches that could be applied here".

**Checker-side specification (§4).** A one-sided Hoare logic `M.WF c vs x Q`, with `Methods.WF` giving:
- `isDefEqCore`: if called on well-typed `e₁ ⤳ e₁'`, `e₂ ⤳ e₂'` and it returns `true`, then `c.IsDefEqU e₁' e₂'`. **Only positive soundness, only on well-typed inputs.** §3.2.4 explicitly disclaims completeness: "Because of various incompletenesses in this algorithm, this doesn't actually imply `s ≇ t`."
- `whnf` / `whnfCore`: `c.TrExpr e e' → (m.whnf e).WF … fun e₁ _ => c.TrExpr e₁ e'` — the specification is stated by *reusing the same* `e'`, "since `⤳` is closed under def.eq."
- `inferType`: does not assume a well-formed input, but does need `e.FVarsIn s.ngen.Reserves` (the fvar counter is fresh); if `inferOnly = true` it additionally assumes `∃e'. TrExpr e e'`.

Verified so far in the paper: only a few functions, `inferLambda` being the worked example (`inferLambda.WF`, and the gnarly `inferLambda.loop.WF` with its 8 invariant hypotheses about the `MLCtx` of `Expr × VExpr` pairs).

**Termination is deliberately not proved; fuel is used.** §3.2.1: the mutual call graph has feedback-vertex-set number 4 (`isDefEqCore`, `whnf`, `whnfCore`, `inferType`), broken via a `Methods` record and `RecM := ReaderT Methods M`. Reasons given for fuel: (i) Gödel — "anything that would imply the unconditional soundness of Lean won't be directly provable"; (ii) **"the Lean type theory is known not to terminate"**, with the Abel–Coquand construction reproduced as actual Lean code (`om`/`Om` via `propext` and `cast`, showing whnf nontermination, and a `Foo : Prop` wrapper showing `isDefEq` nontermination) — "a combination of impredicativity, proof irrelevance, and subsingleton elimination". Fuel is a fixed 1000 and is "only consumed when making a recursive call that is not otherwise decreasing".

**Known unsound assumption still in place** (§4.1): `looseBVarRange_eq`. `looseBVarRange` is implemented by masking 20 bits out of `Expr.data`; the overflow check used `panic!`, which returns `0` for `UInt64` — the worst answer, since it enables `hasLooseBVars = false` optimisations. The bug was found "entirely theoretically, by failing to prove a theorem and working backwards to an actual exploitable soundness bug", and reported/fixed upstream by making `Expr.data` opaque — but "we are still relying on an unsound assumption (`looseBVarRange_eq`)".

Also §3.2.3: Lean4Lean **adds a check the C++ kernel does not do** — when `Nat.add` etc. is added to the environment it verifies `a + 0 ≡ a` and `a + succ n ≡ succ (a + n)`, so the GMP fast path can be proved to compute correctly on literals. Footnote 13: "The original Lean kernel does not perform these checks. This is technically unsound." And `reduceBool` is "simply unsound by design" and unsupported.

### (c) How does it treat the untyped-conversion problem?

**It doesn't have one — the spec's definitional equality is typed, by force.** §8 (Related work), comparing to MetaRocq:

> "Unlike in Lean4Lean, the conversion relation is **untyped**: there is no mutual induction between typing and definitional equality, which **massively simplifies matters**. **In Lean this is unfortunately not an option because of the `t-proof-irrel` rule**, which is expressed in a different way in Rocq."

(Also noted there: MetaRocq's conversion is a *partial order* because of cumulativity, so Conjecture 2.7 "doesn't hold as stated" there, though "principal types" plays the same role; and "Lean's typechecker is known not to be complete, owing to some of the undecidability results in [6], but MetaRocq has a proof of completeness.")

So: **the untyped algorithmic conversion of the actual kernel is related to a *typed* declarative spec, exactly the "term-directed typed conversion" situation Lennon-Bertrand describes** — and Carneiro pays for it with the mutual typing/defeq induction that broke the stratification argument.

### (d) Current status of the metatheory (repo state as of commit `8223d223`, 2026-08-29)

This is more advanced than the paper and is directly relevant to you. `Lean4Lean/Theory/Typing/` contains `Basic, ChurchRosser, Env, EnvLemmas, HeadReduction, InductiveLemmas, Injectivity, Lemmas, Meta, Pattern, QuotLemmas, Strong, UniqueTyping`.

**`Injectivity.lean` (34 lines, 3 `sorry`s)** carries the file comment:
```
/-!
A bunch of important structural theorems which we can't prove :(
-/
```
`IsDefEqU.sort_inv` — `sorry`. `IsDefEqU.forallE_inv_stratified` — `sorry`. `IsDefEqU.sort_forallE_inv` — `sorry`. `forallE_inv` is *derived* from `forallE_inv_stratified` via `IsDefEq.strong` + `stratify`. **Your sort-coherence statements are, in the most advanced Lean-kernel metatheory that exists, still open.**

**`UniqueTyping.lean` (279 lines, 1 `sorry`)**: `IsDefEq.uniq` (paper Conjecture 2.7) **is now proved**, but *modulo* `Injectivity`'s sorries — it calls `IsDefEqU.sort_inv` in its main induction. The mechanism is `HasTypeStratified` from `Strong.lean` (1180 lines, **0 sorries**), which defines `IsDefEqStrong`/`HasTypeStrong` — a re-indexed judgment carrying enough extra data that the substitution lemma (`IsDefEqStrong.instN`) goes through, i.e. the fix for the `max(i,j)` vs `i+j` failure described in §2.4. The one remaining `sorry` there is inside `IsDefEqU.weakN_iff` — **strengthening (Conjecture 2.10) is still open**.

**`ChurchRosser.lean` (1386 lines, 2 `sorry`s)** — the in-progress attack on injectivity, and the most instructive file for your problem:
- Reduction is **typed and context-indexed**: `inductive ParRed : List VExpr → VExpr → VExpr → Prop` with `Γ ⊢ e ≫ e'`. It is *not* a raw-term relation, because of the `extra` constructor:
  ```
  | extra : Pat p r → p.Matches e m1 m2 → r.2.OK (IsDefEqU env univs Γ) m1 m2 →
            (∀ a, Γ ⊢ m2 a ≫ m2' a) → Γ ⊢ e ≫ r.1.apply m1 m2'
  ```
  The side condition `r.2.OK (IsDefEqU env univs Γ) m1 m2` is a **definitional-equality check in Γ** — iota rules are represented as `Pattern`s with defeq-checked pins, abstracted behind a `class Params` (`pat_simple`, `pat_uniq`, `pat_wf`, `pat_app_l`, `pat_app_l_uniq`, `pat_app_uniq`, `extra_pat`). So reduction is intrinsically context- and typing-dependent; a raw untyped Church–Rosser is not even statable here.
- Confluence is proved **up to `NormalEq` (`Γ ⊢ e₁ ≡ₚ e₂`), not syntactic equality.** `NormalEq` is an inductive with constructors `refl, sortDF, constDF, appDF, lamDF, forallEDF, etaL, etaR, proofIrrel` — every constructor carries typing premises, e.g.
  ```
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ₚ h'
  ```
  **This is Carneiro's concrete answer to "proof irrelevance is not a congruence on untyped terms": don't try to make it one. Bake proof-irrelevance and η into an inductively-defined "normal equality", prove *that* transitive separately (`NormalEq.trans`, requiring `OnCtx Γ (IsType env univs)`), and run Takahashi's argument up to it.**
- `ParRed.triangle (H1 : Γ ⊢ e : A) (H : Γ ⊢ e ≫ e') (H2 : Γ ⊢ e ⋙ o) : ∃ o', Γ ⊢ e' ≫ o' ∧ Γ ⊢ o' ≡ₚ o` — Takahashi's optimal reduct is `CParRed` (`⋙`), with a `NonNeutral Γ e` guard on the non-firing cases. `CParRed.exists (H : Γ ⊢ e : A)` — **the optimal reduct only exists for well-typed terms.**
- `ParRed.church_rosser (H : Γ ⊢ e : A)`, then `CRDefEq Γ e₁ e₂ ≜ (∃A, Γ ⊢ e₁ : A) ∧ (∃A, Γ ⊢ e₂ : A) ∧ ∃ e₁' e₂', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₂ ≫* e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂'`, culminating in `IsDefEq.church_rosser (H : Γ ⊢ e₁ ≡ e₂ : A) : Γ ⊢ e₁ ≫≪ e₂`.
- The 2 remaining `sorry`s are both in `NormalEq.parRed`, in the `extra` cases (`constDF`/`extra` and `appDF`/`extra`) — i.e. **the interaction between environment defeqs/iota rules and normal-equality is the last gap.**
- **Import-graph caveat I verified:** `ChurchRosser.lean` imports `UniqueTyping` (which imports `Injectivity`). So the CR development currently *consumes* the injectivity sorries rather than discharging them; the loop is not yet closed. `Lean4Lean/Theory.lean` and `HeadReduction.lean` are the only importers of `ChurchRosser`.

**`HeadReduction.lean` (696 lines, 0 sorries)**: typed weak-head reduction `Γ ⊢ e ⤳ e'` (`WHRed`) with `WHRed.determ`, `WHNF`, `WHRedS`, a `StRed` "strong reduction" relation, and an inference relation `Γ ⊢ e ▷ A` (`InferType`) — the abstract spec of the kernel's `inferType`.

**Directly on your pain point — I grepped the whole repo:**
```
ParRed.weakN_inv   (W : Ctx.LiftN n k Γ Γ') (h : Γ' ⊢ e1.liftN n k : A)
                   (H : Γ' ⊢ e1.liftN n k ≫ e2') : ∃ e2, Γ ⊢ e1 ≫ e2 ∧ e2' = e2.liftN n k
WHRed.weakU_inv    (W : Ctx.Lift' ρ Γ Γ') (H : Γ' ⊢ e1.lift' ρ ⤳ e2')
                   : ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳ e2
WHRedS.weakU_inv, InferType.weakU_inv, InferType.weak'_inv, InferTypeS.weakU_inv
```
**Every backward simulation in lean4lean is along a *renaming* (`liftN` / `lift' ρ`), never along a general substitution. `grep` for `instN_inv | inst_inv | instN_iff` returns nothing in the entire repo.** Note also that `ParRed.weakN_inv` still takes a typing hypothesis for the *lifted* term. This is direct, mechanised confirmation of your diagnosis: the backward direction is available for injective renamings and is simply not attempted for substitutions.

---

## TOPIC 3 — Abel/Öhman/Vezzosi and the Coq port

**Abel, Öhman, Vezzosi, "Decidability of Conversion for Type Theory in Type Theory", POPL 2018, PACMPL 2(POPL):23** — <https://www.cse.chalmers.se/~abela/popl18.pdf>, DOI 10.1145/3158111 (read).

- **Algorithmic conversion is fully typed / type-directed.** The judgments (§4.1) are `Γ ⊢ n ←→ m : A` and `Γ ⊢ n ←̂→ m : A` (neutral comparison, type is an *output*), `Γ ⊢ A ⇐⇒ B` / `⇐̂⇒` (types), `Γ ⊢ t ⇐⇒ u : A` / `⇐̂⇒` (terms); the hatted variants "enforce Whnf" of the type and/or the terms. `Lemma 4.3 (Soundness)`: any algorithmic judgment implies the corresponding declarative judgment.
- **Reduction itself is typed**, which is the key structural choice (§2, and stated as a contribution: "Meta-theory based on typed weak head reduction"). Judgment `Γ ⊢ t −→ u : A`. §2:

  > "the reduction rules are typed, which is one of the main technical innovations of Abel, Coquand, and Manna [2016]. **We immediately get that reduction is included in conversion. In contrast, with untyped reduction, we would need a type preservation (aka subject reduction) theorem which requires function type injectivity (aka Π injectivity) which in turn needs proof by a logical relation.**"

  Concretely `Lemma 2.2 (Reduction subsumed by equality)` and `Lemma 2.3 (Subject typing)` are one-line inductions; the converse (`Γ ⊢ A −→ B ⇒ Γ ⊢ B`) only arrives as a consequence of the fundamental theorem (Thm 3.26). They also note typed reduction "is more flexible … and could be equipped with type-directed reduction rules needed in extensions … by singleton types or strict equality."
- **Generic reducibility is the organising device.** §3.1: a single inductive–recursive Kripke logical relation is parameterised by a "generic equality" `Γ ⊢ t ≅ u : A` satisfying a list of properties (contains neutral equality, PER, closed under weakening, …). The fundamental lemma is proved once and **instantiated twice**: Instance 1 = judgmental equality → gives canonicity and **injectivity of type formers**; Instance 2 = algorithmic equality → gives **completeness of the algorithm**. Termination/decidability then follows.
- So: soundness is a direct induction (cheap, because reduction is typed); *completeness* is the expensive half and is where the logical relation is spent.

**Adjedj, Lennon-Bertrand, Maillard, Pédrot, Pujet, "Martin-Löf à la Coq", CPP 2024, arXiv:2310.06376** — <https://arxiv.org/pdf/2310.06376> (read). The Coq port of the above, and it **deliberately reverses the typed-reduction choice**:

> "Our model relies on an **untyped small-step reduction**. That is, even though at times we bundle big-step reduction proofs with side-conditions that one or both sides are well-typed, we do not ask for typing proofs at the granularity of single reduction steps. **As a result, subject reduction is a result that becomes available late, after the fundamental lemma has been proven.** Since this goes against the position explicitly advocated for in [Abel, Öhman, et al. 2017], we believe this design choice deserves some discussion." (§4.3)

Their two reasons: (i) engineering — "asking for a typed reduction duplicates the definition of typing derivations into a reduction variant … too unpractical"; (ii) theoretical — "opting for typed reduction hardwires a specific kind of models … Since typed reduction implies typing in the declarative system, and the logical relation implies reduction to a normal form, it is essentially asking that the resulting model is complete for declarative typing", which rules out instances like "the instance used to prove untyped weak-head normalization of well-typed terms, which interprets all typing statements trivially."

Also §4.4, worth knowing: "the declarative instance of the logical relation does **not** show that neutral destructors are injective … This is the core reason why we must instantiate the logical relation with **algorithmic** instances … The declarative instance also does not imply deep normalization, again because it does not go under neutrals." They also removed induction–recursion (Coq lacks it), using indexed inductives + universe-level indexing `ℓ ∈ {0,1}` instead.

**Historical anchor for typed-vs-untyped equivalence:** Siles & Herbelin, "Pure Type System conversion is always typable", JFP 22 (2012) 153–180 — <https://inria.hal.science/inria-00497177/en>. This (not any Winterhalter paper) is the general PTS result that untyped-conversion and judgmental-equality presentations coincide; *Touring the MetaCoq Project* §6.2 cites it as the basis for a future "prove the theory is equivalent to a variant where conversion is typed" work item, "updating them to handle cumulativity".

---

## Synthesis: what this says about your specific blocker

I want to be careful to separate what the literature says from my inference. The following are my inferences, flagged as such, but each rests on a quoted fact above.

1. **Your false lemmas are expected.** No project in this space proves a backward simulation "reduction of the substituted term ⇒ reduction of the original". MetaCoq avoids needing it by making conversion untyped and getting inversions from **confluence**; Abel et al. avoid it by making **reduction typed**; lean4lean only ever inverts along **renamings** (`weakN_inv`/`weakU_inv`, grep-verified). The substitution direction is proved forward only (MetaCoq Thm 2.1 parallel substitution; lean4lean `ParRed.instN`, `NormalEq.instN`).

2. **The statement you probably want instead of a simulation is Abel–Altenkirch standardisation, as reported by Lennon-Bertrand §5:** *if a term is convertible to a weak-head normal form, it weak-head-reduces to a weak-head normal form of the same shape.* Combined with Lennon-Bertrand's **Property 1 + Corollary 3 ("types classify normal forms")**, that is exactly "when defeq succeeds, both sides agree on sort/Pi-structure" — and Fig. 1 of that paper certifies that **injectivity of type constructors alone suffices for positive soundness, with no normalisation needed**.

3. **Don't try to make proof irrelevance a congruence.** Both mature responses are the same shape: put it in a *typed*, inductively-defined "normal/algorithmic equality" and prove transitivity of that relation separately. lean4lean does this literally (`NormalEq.proofIrrel` with three typing premises; `NormalEq.trans` under `OnCtx Γ (IsType env univs)`; confluence stated up to `≡ₚ` rather than `=`). Lennon-Bertrand §4.4 independently confirms the implementation-side consequence: proof irrelevance destroys completeness of neutral comparison, and Lean's kernel copes by **re-inferring types of neutrals on failure**.

4. **Well-typedness as a precondition is the norm, not a cop-out.** MetaCoq makes it a *function argument* (the algorithm doesn't type-check without it). Lennon-Bertrand makes it an explicit precondition table (Fig. 6) and explicitly refuses to re-check invariants at runtime ("constantly re-checking context well-formation … is terrible for performance"). lean4lean's `Methods.WF` assumes `TrExpr` (well-typed translation) for `isDefEqCore` and `whnf`. If your intermediate states after substituting telescope entries can't carry a well-typedness invariant, that — not the missing simulation — is likely the real design problem.

5. **Two transferable proof-engineering recipes.** (i) Lennon-Bertrand's *local preservation lemmas* — one per rule, metaprogrammed, assembled into a "bundled induction principle" that threads invariants as extra hypotheses (§4.1). (ii) Carneiro's `Strong.lean` — a re-indexed `IsDefEqStrong`/`HasTypeStrong` judgment carrying enough data that `instN` (substitution) goes through, which is exactly the repair for the stratification-vs-substitution failure described in the paper's §2.4. `Strong.lean` is 1180 lines and 0 sorries.

6. **Your project's position is unusual and possibly advantageous.** Every project surveyed targets a *syntactic* spec. Lean4Lean §9 defers the model. MetaCoq's Trusted Theory Base is "PCUIC typing rules + SN". You are going to a set-theoretic model directly, which sidesteps unique typing (Carneiro §2.4: "there are alternative routes to construct the model that avoid unique typing"). But note his very next sentence: "these conjectures are necessary in at least some form **in order to prove the correctness of the typechecker**". So a model route may buy you consistency without buying you the checker-correctness lemmas.

---

## Load-bearing facts I verified (read in the source myself)

- PCUIC's conversion is **untyped, on raw terms**, defined as the closure of reduction up to α-cumulativity (*Touring* §2.2.1); typing touches it only via `type_Cumul` (*Coq Coq Correct!* Fig. 2).
- MetaCoq's reduction and conversion are **defined by well-founded recursion on accessibility derived from the SN axiom restricted to well-typed terms**, with `wellformed Σ Γ (zip t)` as a function argument; no fuel (*CCC* §3.1–3.2, `R_Acc`, `reduce_stack`).
- MetaCoq correctness is **by construction via subset types**; POPL 2020 did **not** prove completeness of type inference (*CCC* §3.5).
- MetaCoq axioms: SN of PCUIC on well-typed terms + guard/positivity oracles + (in 2020) subject reduction, validity, strengthening in progress (*CCC* §2.3.4, Fig. 5, footnote 3; *Touring* §5, §6.1).
- Confluence via parallel reduction + Takahashi triangle, and it is explicitly what supports Π-injectivity and equivalence of undirected conversion with joinability (*CCC* §2.3.2; *Touring* §3.2.3).
- MetaCoq needs a **separate** context-confluence argument because of let-in "action at a distance" (*CCC* §2.3.2).
- Lennon-Bertrand FSCD 2025: Fig. 1 dependency table; Property 1; Corollary 2 (preservation from injectivity alone); Corollary 3 (types classify normal forms); Fig. 6 precondition table; Props 13–24; the "untyped conversion = term-directed typed conversion" thesis; typed needs only Property 9 while untyped needs Property 7; Prop 22's use of **strengthening** (not simulation); §4.4 on SProp/unit-η and Lean's re-inference strategy; §5's report of Abel–Altenkirch standardisation.
- Lean4Lean paper: single `IsDefEq` judgment; Fig. 1 rules incl. t-proof-irrel and t-extra; Lemmas 2.1–2.6 proved; **Conjectures 2.7, 2.9, 2.10** open; the stratification-vs-substitution error (`max(i,j)` vs `i+j`); FVS-4 `Methods`/`RecM` fuel design with fuel = 1000; the Abel–Coquand nontermination witness in Lean; `Methods.WF` giving positive-soundness-only for `isDefEqCore`; §4.1 `looseBVarRange` bug and the still-unsound `looseBVarRange_eq`; §3.2.3 Nat-op recurrence checks the C++ kernel omits; §8's statement that Lean cannot use untyped conversion "because of the t-proof-irrel rule".
- Lean4Lean repo at `8223d223` (2026-08-29): `Injectivity.lean` = 3 sorries with the comment "theorems which we can't prove :("; `UniqueTyping.lean` proves `uniq` modulo those, 1 remaining sorry in `weakN_iff` (strengthening); `Strong.lean` and `HeadReduction.lean` 0 sorries; `ChurchRosser.lean` = typed context-indexed `ParRed` with a defeq-side-conditioned `extra` rule, `NormalEq` with an explicit `proofIrrel` constructor, `NormalEq.trans`, `ParRed.triangle`, `IsDefEq.church_rosser`, 2 sorries in `NormalEq.parRed`'s `extra` cases; ChurchRosser imports UniqueTyping so the injectivity loop is not yet closed; **no substitution-inversion lemma exists anywhere in the repo — only `weakN_inv`/`weakU_inv` along renamings.**
- Abel/Öhman/Vezzosi: typed algorithmic equality; **typed weak-head reduction** chosen precisely to avoid needing subject reduction / Π-injectivity up front; generic equality instantiated twice (judgmental → injectivity+canonicity; algorithmic → completeness).
- Adjedj et al. (CPP 2024) deliberately switched to **untyped** small-step reduction, so subject reduction "becomes available late, after the fundamental lemma", with both reasons stated verbatim; and the declarative instance of the logical relation does not give neutral-destructor injectivity or deep normalisation.
- Siles & Herbelin (JFP 2012) is the general PTS typed/untyped-conversion equivalence result; *Touring* §6.2 lists extending it to cumulativity as future work.

## Things I could NOT verify

- **The JACM 2025 paper's actual text.** "Correct and Complete Type Checking and Certified Erasure for Coq, in Coq", J. ACM 72(1) Art. 8, DOI 10.1145/3706056 — ACM returned 403 and the HAL preprint (hal-04077552) is behind an Anubis challenge. My statements that it adds **completeness** rest on (i) the lean4lean paper §8 ("MetaRocq [15,25] has a proof of completeness") and (ii) the MetaRocq README as summarised by a fetch tool. **I did not read the completeness theorem statement.** Its precise preconditions are unknown to me.
- **A Winterhalter paper on typed vs. untyped conversion.** I searched and found none. Winterhalter's relevant contributions are: his PhD thesis *Formalisation and meta-theory of type theory* (Université de Nantes, 2020, <https://theowinterhalter.github.io/#phd>), whose chapters 23–24 contain the dependent lexicographic order modulo used for MetaCoq's conversion termination (per Lennon-Bertrand §4.1, who adds that Winterhalter "admits that his setup would not easily incorporate η-expansion"), and `PartialFun` (the free recursion monad used by the FSCD paper). **The paper you were thinking of is almost certainly Lennon-Bertrand FSCD 2025, and/or Siles–Herbelin JFP 2012.**
- **Anything named "backward simulation of substituted reduction" in the literature.** I searched for anti-substitution / reduction-reflection lemmas of the form `t[σ] ↠ u ⇒ t ↠ …` and found no usable citation. The nearest thing I *can* ground is (a) the renaming-only inversions in lean4lean, and (b) Lennon-Bertrand's **strengthening** lemma, which is the substitution-flavoured property that actually gets proved (for algorithmic judgments, where it is easy; he says it is "generally difficult to prove for declarative systems"). **I am fairly confident, but did not find an explicit statement in print, that the general backward simulation is regarded as simply false and is therefore never stated.**
- **Whether proof irrelevance is or is not a congruence on untyped terms** as a published theorem. Lennon-Bertrand §4.4 discusses the *consequences* (wrecked completeness of neutral comparison) and describes workarounds, but explicitly leaves the extension of his framework to strict propositions as future work. lean4lean's `NormalEq.proofIrrel` is typed, which is evidence for your claim but not a proof of it.
- **Lean4Lean's `Verify/` layer status.** I counted 131 `sorry`s repo-wide across 27 files, including `Verify/TypeChecker/{IsDefEq,InferType,WHNF,Reduce}.lean`, but I did not audit which specific theorems are open there, nor did I build the project.
- **Abel & Altenkirch's standardisation theorem itself.** I have it only via Lennon-Bertrand §5's characterisation; I did not read *A partial type checking algorithm for type:type* (ENTCS 229(5), 2011). **If standardisation is the lemma you want, read that paper directly before relying on my paraphrase.**

Sources:
- [Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq (POPL 2020)](https://sozeau.gitlabpages.inria.fr/www/research/publications/Coq_Coq_Correct-POPL20.pdf)
- [Touring the MetaCoq Project (arXiv:2107.07670)](https://arxiv.org/pdf/2107.07670)
- [What does it take to certify a conversion checker? (FSCD 2025, arXiv:2502.15500)](https://arxiv.org/pdf/2502.15500)
- [Correct and Complete Type Checking and Certified Erasure for Coq, in Coq (JACM 2025) — metadata only](https://dl.acm.org/doi/10.1145/3706056)
- [MetaRocq repository](https://github.com/MetaRocq/metarocq)
- [Lean4Lean: Verifying a Typechecker for Lean, in Lean (arXiv:2403.14064v3)](https://arxiv.org/pdf/2403.14064)
- [lean4lean repository](https://github.com/digama0/lean4lean)
- [Decidability of Conversion for Type Theory in Type Theory (POPL 2018)](https://www.cse.chalmers.se/~abela/popl18.pdf)
- [Martin-Löf à la Coq (CPP 2024, arXiv:2310.06376)](https://arxiv.org/pdf/2310.06376)
- [Pure Type System conversion is always typable (JFP 2012)](https://inria.hal.science/inria-00497177/en)
- [Théo Winterhalter, PhD thesis](https://theowinterhalter.github.io/#phd)