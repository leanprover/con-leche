# Literature report: partiality, convergence, and code-indexing in NbE/logical-relation verifications

Everything below is grounded in a source I actually fetched and read. Section/lemma numbers are from the fetched documents. A "verified / could not verify" split is at the end.

---

## TOPIC 1 — Abel-style typed NbE and PER models

**Primary source:** Andreas Abel, *Normalization by Evaluation: Dependent Types and Impredicativity*, Habilitation thesis, LMU München, 2013. PDF: https://www.cse.chalmers.se/~abela/habil.pdf (downloaded and text-extracted; page/section numbers below are the thesis's own).

### (a) How is partiality of the evaluator treated?

Abel uses **partial applicative structures**, and then **inductively-defined graphs** when the treatment has to be type-theoretic. Both, in that order.

§3.2 "Untyped NbE Using Partial Applicative Structures", p. 20:

> "For our purposes, a partial applicative structure is a set D with partial application operation `· ∈ D × D ⇀ D` and partial evaluation operation `[[ ]]( ) ∈ Exp × Env ⇀ D` where `Env = N ⇀ D`."

The defining axioms are stated **modulo Kleene equivalence**:

> "We read these equations as: if one side is defined, so is the other, and then both are equal (Kleene equivalence `≐`)."

Then, immediately, the move to relations (p. 21):

> "Still, we are using partial functions which might be a convenient tool of set theory but are not a primitive notion in type theory. A principled method [Bove et al., 2013] to construct a partial function in type theory is to first define the graph of the function inductively and then construct the 'partial' function by recursion over its inductive graph. The graphs of application and evaluation are given by the mutual inductive relations `f · a ↘ b` and `[[t]](ρ) ↘ a`."

with a footnote: *"In fact, this 'partial function' is a total function, but its domain is not the full product of argument types."*

Readback is partial too, for the same reason, and gets the same treatment: `Rⁿᶠ_n d ↘ v`, `Rⁿᵉ_n e ↘ u` are inductive relations, "since read-back of closures triggers the evaluation of the function body". NbE itself is then **relation composition**: `nf_n(t) ↘ v :⟺ [[t]](ρ_n) ↘ d and Rⁿᶠ_n d ↘ v`.

So: **not fuel, not a delay monad, not coinduction. Big-step inductive graph relations (Bove–Capretta style), with a partial-function reading available on paper via Kleene equivalence.** The summary chapter (§6, p. 67) reiterates that the whole development is framed in "(syntactical) partial applicative structures", of which domains, closures, whnfs, and compiled code are all instances.

Danielsson's coinductive approach is *not* used; Danielsson is cited elsewhere in the thesis (§6.1, p. 69) only for intrinsically-typed NbE, not for partiality.

### The decisive point for your design question: convergence is *baked into membership*

This is the most directly relevant passage in the whole thesis. §3.3 "Type-Assignment System T", p. 22:

> "Evaluation is now partial not only because of non-termination, but also because of illegal operations; for instance, application of a number to an argument is undefined, as well as recursion over a closure instead of a number. In the following, we identify sets of values on which application and recursion are well-behaved and terminating. These sets of values are semantic types."

and then, verbatim:

> `A → B = {f ∈ D | ∀a ∈ A. ∃b ∈ B. f · a ↘ b}`
>
> "Let us introduce some suggestive, abbreviating notation for the statement that one of our operational relations produces a result in some semantic type. We write
> `f · a ∈ B` iff `∃b ∈ B. f · a ↘ b`
> `rec(d_z, d_s, d_n) ∈ B` iff `∃b ∈ B. rec(d_z, d_s, d_n) ↘ b`
> `[[t]](ρ) ∈ B` iff `∃b ∈ B. [[t]](ρ) ↘ b`"

**That is exactly option (b)-baked-in.** `[[t]](ρ) ∈ B` is *defined* as an existential "evaluates-to-and-lands-in-B". There are no convergence side premises anywhere downstream; every semantic-typing judgment carries convergence as part of its meaning. Convergence of the *whole* NbE pipeline is then a *derived* fact, not a hypothesis (§3.4, p. 25): the candidate space is

> `⊤ = {d | ∀n ∃v ∈ Nf. Rⁿᶠ_n d ↘ v}`, `⊥ = {e | ∀n ∃u ∈ Ne. Rⁿᵉ_n e ↘ u}`

— again pure existential-convergence sets — "Now every semantic type contains only reifiable values... thus `Rⁿᶠ_n([[t]](ρ_n)) ↘ v` for some `v ∈ Nf`, and we have established the normalization of typable terms."

### Do the PERs relate only values?

Yes. §3.6 (p. 27): a PER is "a symmetric and transitive relation `A ⊆ D × D`", i.e. a relation **on the value domain D**, not on terms. Term-level equality is then *derived* by composing with evaluation (p. 30):

> `ρ = ρ' ∈ [[Δ]]  :⟺ ∀i. Δ(i) = T ⟹ ρ(i) = ρ'(i) ∈ [[T]]`
> `Γ ⊨ t = t' : T  :⟺ ∀ρ = ρ' ∈ [[Γ]]. [[t]](ρ) = [[t']](ρ') ∈ [[T]]`

Under the §3.3 convention, `[[t]](ρ) = [[t']](ρ') ∈ [[T]]` asserts that both evaluations converge and the results are related. Convergence lives *inside* the semantic judgment, not beside it.

The dependent version (§4.4, p. 46) is the same shape:

> "In the following, let us write `L M ∈ Exp × Env → D` for the partial function that performs evaluation of expressions into D."
> `Γ ⊨ t = t' : T  :⟺  Γ ⊨ T  and  ∀ρ = ρ' ∈ [[Γ]]. LtMρ = Lt'Mρ' ∈ [[T]]ρ`

### (b) Is transitivity free, or does it need determinism?

**On paper in Abel's habilitation: free, because evaluation is stipulated to be a partial *function*.** The word "deterministic" does not occur in the thesis at all (I grepped). The reason is structural: the partial applicative structure *defines* `·` and `[[ ]]` as partial functions, so `[[t]](ρ)` denotes at most one value by fiat; the PER laws (symmetry + transitivity) are then established purely at the level of value relations. §3.6 (p. 27–30): PERs are subgroupoids of `D × D` ("symmetry corresponding to inversion and transitivity to concatenation"), and the semantic function space `A → B` is shown to be a subgroupoid whenever `A` and `B` are. §4.4 (p. 45–46): "If A is a PER and `F ∈ A → Per`, then `Π A F` is also a PER... Simultaneously with the definition, we also prove that the universes `Set_k` are indeed PERs."

**Once you re-encode evaluation as an inductive graph relation — which is what every mechanization does, and what a fueled machine effectively is — this freeness evaporates and determinism becomes a load-bearing lemma.** See Topic 2: both AÖV (Lemma 2.5 + Lemma 3.9) and McTT (`functional_eval` used inside the transitivity/irrelevance proofs) need it explicitly. This is, I think, the single most useful fact for your design decision, and it is invisible in the pen-and-paper literature precisely because Abel takes evaluation to be a function.

Abel does flag one related subtlety (§3.6, p. 55 area, on the groupoid/MAG approach): closing a PER under a partial chaining operation "squashes the PER structure" — i.e. partiality of the underlying operation does interact badly with PER structure when you try to be clever. He calls that route "only a sketch".

### (c) Precedent for code-indexed / Tarski-style-universe-indexed logical relations

**Yes — this is the standard Abel/Coquand/Dybjer construction, and it is exactly "codes".**

Habilitation §4.3 (p. 45), the subset model:

> "We will now inductively define a sequence `Set_0, Set_1, …` of universes which are semantic types themselves and **contain valid codes for types**. At the same time, we define the extension functions `El_i ∈ Set_i → P(D)` that map valid type codes to semantic types. The joint definition of `Set_i` and `El_i` is called an **inductive-recursive** definition [Dybjer, 2000]."

Codes are `N`, `Set_j`, `Fun A F`; extension is `El_k(N) = Nat`, `El_k(Set_j) = Set_j`, `El_k(Fun A F) = Π A F`. §4.4 redoes this at PER level, adding neutral codes `↑^{Set_k} E`, with `El_k(E) = E`.

And the *logical relation* is literally indexed by codes. §4.7 (p. 51), "Kripke Logical Relations for Dependent Types and Soundness of NbE":

> "In case of dependent types, we cannot just do induction on type expressions, but **we can induct on type values `A ∈ Set_k` instead**. This induction is the privilege of predicative type theory where types are obtained from below."
>
> "By induction on `A ∈ Set_k` we define a relation `Γ ⊢ T Ⓡ A` between well-formed types and type values, and a relation `Γ ⊢ t : T Ⓡ a ∈ A` between well-typed terms and values `a ∈ [A]`."

Also §4.5 "dependently-typed candidate spaces": "a pair of semantic types `A̲`, `A̅` **for each type code `A ∈ U**`", with a realizability relation `A ⊩ 𝒜` ("`A̲ ⊆ 𝒜 ⊆ A̅`"), proven by induction on `A ∈ Set_k`.

The earlier, canonical presentation is **Abel, Coquand, Dybjer, "Normalization by Evaluation for Martin-Löf Type Theory with Typed Equality Judgements", LICS 2007**, PDF: https://www.cse.chalmers.se/~peterd/papers/NbeMLTTEqualityJudgements.pdf — §3.1–3.2. There, codes are values `N`, `Fun X F`, `U`, `Up u` in a combinatory algebra, and:

> "We then give a simultaneous inductive-recursive definition of the PERs `U` and `[d]`. … we can e.g. follow [6,1] and **inductively define the graph of a partial function `[ ] : D ⇀ Rel(D)`** such that the following equations hold: `[Up u] = …`, `[N] = N`, `[Fun X F] = {(f,f') | (f d, f' d') ∈ [F d] for all (d,d') ∈ [X]}`."
>
> "To prove univalence of this relation we use that `Up`, `N`, and `Fun` are constructors. … We then show by induction on this relation that **if `X = X' ∈ U` then `[X]` and `[X']` are well-defined and equal PERs**."

That last sentence is *your* code-uniqueness lemma, in its original form. Note what makes it go through: injectivity of the code constructors, plus the fact that `[ ]` is a partial function whose graph is inductively defined — i.e. functionality of the code→relation assignment is a *proved* property of an inductively-defined graph, not an assumption.

**Same pattern in Abel/Vezzosi/Winterhalter**, *Normalization by Evaluation for Sized Dependent Types*, PACMPL 1(ICFP):33, 2017, long version PDF: https://www.cse.chalmers.se/~abela/icfp17-long.pdf. Their `Ne`, `Nf`, `Elim`, `Ty` PERs are defined with existential readback clauses, §"Partial equivalence relations", p. 1:17:

> `n = n' ∈ Ne :⟺ Rᵏₙₑ n ↘ m and Rᵏₙₑ n' ↘ m' and m ≈ m' for all k`

— convergence baked in, again. And determinism *does* surface once evaluation is a relation: two proofs in their appendix read "By cases on D, since **weak head evaluation is deterministic**."

---

## TOPIC 2 — Mechanized precedents

### 2.1 Abel, Öhman, Vezzosi, *Decidability of Conversion for Type Theory in Type Theory*, POPL 2018 (PACMPL 2(POPL):23)

PDF: https://www.cse.chalmers.se/~abela/popl18.pdf (also https://dl.acm.org/doi/10.1145/3158111). Agda, ~10k lines.

**How they avoid the partiality problem: there is no evaluator.** They do not use an environment machine at all; the meta-theory is built on a **typed weak-head reduction *relation*** `Γ ⊢ t ⟶ u : A` and its reflexive-transitive closure (§2, Fig. 4). Introduction, p. 23:2:

> "Meta-theory based on typed weak head reduction."
> "In Section 2 we define our type theory … along with a **typed weak head reduction relation which we prove deterministic**. Using a typed variant of reduction gives us the soundness of reduction immediately, which is otherwise established by the subject reduction theorem."

A relation is inherently partial (a term may relate to nothing), so partiality costs nothing. Determinism is Lemma 2.5: "Reduction is deterministic; each expression has at most one reduct."

**Convergence is baked in, and normalization is an output not an input.** §3.2:

> "These judgements will imply that all involved objects are reducible (in the sense of weak normalization), in particular, **all involved objects have a weak head normal form**. … This is achieved by **defining the judgements on weak head normal forms and closing them under weak head expansion**."

Every clause is an existential "reduces-to". E.g. at ℕ: `Γ ⊩ℓ t : A / T` iff **there exists a whnf `t̄`** such that `Γ ⊢ t :⟶*: t̄ : ℕ`, `Γ ⊢ t̄ ⊛ t̄ : ℕ`, and `Γ ⊩ℕw t̄`. At neutral type: "iff there is a neutral `n` such that `Γ ⊢ t :⟶*: n : N`". Weak head normalization is then **Theorem 3.28**, derived *from* the fundamental theorem — not assumed.

**What the logical relation is indexed by: a reducibility *derivation*, via induction-recursion.** §3.2, p. 23:12–13:

> "the negative occurrence prevents us to define `Γ ⊩ℓ t : A` as inductive predicate. Instead, we have to define it by **recursion on the derivation `T` of `Γ ⊩ℓ A`, written `T :: Γ ⊩ℓ A`**, which in turn is an inductive predicate. Thus, the term reducibility judgement will depend on `T` and we write `Γ ⊩ℓ t : A / T`. … This definition scheme of interleaving induction and recursion is called induction-recursion."

Plus an outer well-founded induction on the universe level `ℓ ∈ {0,1}`. So the indexing is: **(universe level `ℓ`) × (an inductive derivation `T` witnessing that `A` is a reducible type)** — which is the derivation-shaped cousin of your semantic codes. They then prove the indexing is *irrelevant* a posteriori (Lemma 3.5), so that morally it is indexed by the type only. Their §8 conclusion: "we have managed to show that the a priori proof-relevant definitions are proof-irrelevant a posteriori … Informally, this aspect is often glossed over."

**Transitivity needs determinism — explicitly.** This is the passage most relevant to your question:

> **Lemma 3.9 (Transitivity).** (1) If `Γ ⊩ℓ A :=: A'` and `Γ ⊩ℓ A' :=: A''` then `Γ ⊩ℓ A = A''`. (2) If `Γ ⊩ℓ t = t' : A` and `Γ ⊩ℓ t' = t'' : A` then `Γ ⊩ℓ t = t'' : A`.
> **Proof.** By induction on the shape view (3.3) of type `A, A', A''`, **using determinism of reduction (2.5)**, irrelevance (3.5) and conversion of reducible equality (3.7).

The same for Symmetry (3.8), Conversion (3.7), Irrelevance (3.5), and the "shape view" construction (3.3) itself — determinism of reduction is cited in *every one*. They also built a dedicated device, the **shape view** (Lemma 3.3), whose entire purpose is to discharge, once and for all, the impossible cross-cases (`A ⟶* Π F G` *and* `A ⟶* ℕ`) that determinism rules out: "Pattern matching on proofs of the view then allows us to consider only the compatible cases."

There is a second, *parameterized* PER requirement: the logical relation is parametric in a "generic equality" `⊢ _ ⊛ _`, and **Property 2 (Partial equivalence relation)** demands that the parameter be symmetric and transitive. So transitivity of the *parameter* is an assumption; transitivity of the *logical relation* is a theorem requiring determinism.

### 2.2 Adjedj, Lennon-Bertrand, Maillard, Pédrot, Pujet, *Martin-Löf à la Coq*, CPP 2024

arXiv: https://arxiv.org/abs/2310.06376 (PDF https://arxiv.org/pdf/2310.06376), DOI https://dl.acm.org/doi/10.1145/3636501.3636951.

Direct Coq port of AÖV, so the reduction story is identical: §2, "Our formalization uses **weak-head reduction ⇝, a deterministic reduction strategy**". Convergence baked into the LR the same way (§5: "given any type `A` and a proof `r : A ⇝* ℕ`… the term `t` is reducible if it **weak-head reduces** either to `0`, to a successor `S u` with … or to a neutral term").

**Indexing, made explicit.** They remove induction-recursion via **small induction-recursion** (Hancock et al.). §5, Fig. 1, simplified Coq:

```coq
Definition RedRel@{i} := Con -> Term -> (Term -> Type@{i}) -> Type@{i+1}.
Inductive LR@{i} : ∀ (ℓ : TypeLevel), RedRel@{i} :=
| redU : Γ ⊩U A -> LR@{i+1} 1 Γ A (fun B => ∑ P, LR@{i} 0 Γ B P)
| redℕ : Γ ⊩ℕ A -> LR@{i} ℓ Γ A Redℕ.
Notation "Γ ⊩⟨ℓ⟩ A" := (∑ P, LR ℓ Γ A P).
Notation "Γ ⊩⟨ℓ⟩ t : A / RA" := (fst RA t).
```

> "`LR@{i} ℓ Γ A P` **encodes as a functional relation** the fact that `P : term -> Type@{i}` is the reducibility predicate `Γ ⊩⟨ℓ⟩ _ : A / ℜ_A` associated to the reducibility proof `ℜ_A` in the usual IR presentation."

So the LR relates *(level, context, type, induced-predicate)*. This is structurally the same as "code-indexed with an El function", with the El result carried as a relation parameter rather than computed. Cost: `n+4` universes for `n` object universes.

**Their partiality handling for the *checker* is the cleanest statement of the separation of concerns you care about.** §3, "Partiality and general recursion in type theory":

> "The more traditional approaches to non-structurally recursive functions either rely on well-foundedness, encoded as an inductive accessibility predicate; or on **step-indexing, using an extra 'fuel' parameter** bounding the allowed number of recursive calls. The latter induces significant noise in the definition, while the former makes it impossible to separate the definition of a function from a proof of its termination/totality…
> Our approach, based on [McBride 2015], separates the description of a recursive function from its realization **using a free monad to describe the calling graph. From this monadic object, the fuelled, coinductive or graph-based realization can all be easily recovered**, depending on one's goals."

And §7.2, the three properties they prove, kept strictly apart:

> • **soundness**: if the function returns without raising an error, then the corresponding judgement is derivable;
> • **completeness**: if the corresponding judgement is derivable, then the function always returns a positive result;
> • **termination**: the function always returns a result … when called on inputs satisfying its precondition.
>
> "The first is a **fuelled implementation**, which computes efficiently … we use the fuelled checker and its soundness to derive typing derivations by reflexion. **Note how this only relies on soundness of the functions, but not on their completeness or termination.**"

**Nothing about fuel or convergence enters the logical relation at all.** The LR is stated over the relational, deterministic reduction; the fuelled machine is a separate realization whose only obligation is soundness.

### 2.3 McTT — Jang, Gaulin, Hu, Pientka, *McTT: A Verified Kernel for a Proof Assistant*, PACMPL 9(ICFP):190–221, 2025

DOI https://dl.acm.org/doi/10.1145/3747511 · ICFP page https://icfp25.sigplan.org/details/icfp-2025-papers/7/McTT-A-Verified-Kernel-for-a-Proof-Assistant · repo https://github.com/Beluga-lang/McTT (I read the Rocq sources on `main`; the paper artifact branch is `icfp25`). Per the ICFP abstract: a theoretical component proving "normalization, consistency, and injectivity of type constructors using an **untyped domain model**", and an algorithmic component connecting it to an extracted OCaml implementation. **This is the closest published analogue to your setting** — a real NbE-based kernel, verified end-to-end, with an untyped value domain.

**Evaluation is an inductive relation, and its functionality is a proved lemma that is then used everywhere.**

`theories/Core/Semantic/Evaluation/Definitions.v`: `Inductive eval_exp : exp -> env -> domain -> Prop` with notation `⟦ M ⟧ ρ ↘ m`, mutually with `eval_app` (`$| m & n |↘ r`), `eval_fst`/`eval_snd`, `eval_natrec`, `eval_sub`. No fuel; the graph is the semantics.

`theories/Core/Semantic/Evaluation/Lemmas.v`:

```coq
Lemma functional_eval :
  (forall M ρ m1, {{ ⟦ M ⟧ ρ ↘ m1 }} -> forall m2, {{ ⟦ M ⟧ ρ ↘ m2 }} -> m1 = m2) /\ …
```
plus the tactic `functional_eval_rewrite_clear` that rewrites with it.

**Convergence is baked in, via named "modulo evaluation" bundles.** `theories/Core/Semantic/PER/Definitions.v`:

```coq
(** Related modulo evaluation *)
Variant rel_mod_eval R A ρ A' ρ' R' : Prop := mk_rel_mod_eval :
  forall a a', {{ ⟦ A ⟧ ρ ↘ a }} -> {{ ⟦ A' ⟧ ρ' ↘ a' }} -> {{ DF a ≈ a' ∈ R ↘ R' }} -> …

(** Related modulo application *)
Variant rel_mod_app f a f' a' R : Prop := mk_rel_mod_app :
  forall fa f'a', {{ $| f & a |↘ fa }} -> {{ $| f' & a' |↘ f'a' }} -> {{ Dom fa ≈ f'a' ∈ R }} -> …
```

and, at the top level, `theories/Core/Completeness/LogicalRelation/Definitions.v`:

```coq
Inductive rel_exp M ρ M' ρ' R : Prop := mk_rel_exp :
  forall m m', {{ ⟦ M ⟧ ρ ↘ m }} -> {{ ⟦ M' ⟧ ρ' ↘ m' }} -> {{ Dom m ≈ m' ∈ R }} -> rel_exp …
```

`per_bot`, `per_top`, `per_top_typ` are the same existential shape over readback: `fun m m' => forall s, exists L, {{ Rne m in s ↘ L }} /\ {{ Rne m' in s ↘ L }}`.

**The universe PER is code-indexed, literally.** `per_univ_elem_core : relation domain -> domain -> domain -> Prop`, written `DF a ≈ a' ∈ per_univ_elem i ↘ elem_rel` — it relates two *type values* (codes: `𝕌@j`, `ℕ`, `Π a ρ B`, `Σ a ρ B`, `Eq a m1 m2`, neutral) and simultaneously determines the element relation `elem_rel`. Defined by `Equations per_univ_elem (i : nat) : … by wf i` — well-founded on the universe level, with the small-IR encoding.

**Code-uniqueness is `per_univ_elem_right_irrel`, and its proof is the determinism lemma.** `theories/Core/Semantic/PER/Lemmas.v`:

```coq
Lemma per_univ_elem_right_irrel : forall i i' R a b R' b',
    {{ DF a ≈ b  ∈ per_univ_elem i  ↘ R  }} ->
    {{ DF a ≈ b' ∈ per_univ_elem i' ↘ R' }} ->
    (R <~> R').
Proof with (destruct_rel_mod_eval; destruct_rel_mod_app;
            functional_eval_rewrite_clear; econstructor; intuition).
```

Same for `per_univ_elem_cross_irrel`, and `functional_eval_rewrite_clear` appears throughout the symmetry/transitivity/`PER` instance proofs (`per_univ_PER`, `per_elem_PER`, `per_ctx_PER`, `per_subtyp_trans_ins`). **This is precisely your "transitivity and code-uniqueness need convergence premises" concern, resolved in a real development by (i) baking convergence into the relation and (ii) proving evaluation functional and using that instead.**

**One important nuance — McTT uses *both* shapes, in different relations.** The completeness/PER side is existential (above). The **soundness/gluing** side (`theories/Core/Soundness/LogicalRelation/Definitions.v`) uses a *universally quantified* evaluation premise in the structural clauses:

```coq
| glu_univ_elem_core_pi :
    {{ DG a ∈ glu_univ_elem_core ↘ IP ↘ IEl }} ->
    {{ DF a ≈ a ∈ per_univ_elem i ↘ in_rel }} ->
    (forall {c} (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) b,
        {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->            (* ← ∀, not ∃ *)
        {{ DG b ∈ glu_univ_elem_core ↘ OP _ equiv_c ↘ OEl _ equiv_c }}) -> …
```

while the *top-level* soundness judgment is again existential:

```coq
Variant glu_rel_exp_with_sub i Δ M A σ ρ : Prop := mk_glu_rel_exp_with_sub :
  `{ forall P El, {{ ⟦ A ⟧ ρ ↘ a }} -> {{ ⟦ M ⟧ ρ ↘ m }} ->
       {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
       {{ Δ ⊢ M[σ] : A[σ] ® m ∈ El }} -> … }.
```

So the design pattern in practice is: **∃ at the judgment boundary (convergence is a conclusion you can consume), ∀ inside structural clauses (convergence is a hypothesis you can assume)** — and determinism reconciles the two directions. Both are cheap only because `functional_eval` exists.

Also worth noting for your `initial_env`: McTT proves `functional_initial_env` for the same reason, and `nbe` itself is an `Inductive nbe : ctx -> exp -> typ -> nf -> Prop`, i.e. a relation, with the executable version in `theories/Extraction/NbE.v`.

### 2.4 Wieczorek & Biernacki, *A Coq Formalization of NbE for MLTT*, CPP 2018

DOI https://dl.acm.org/doi/10.1145/3167091 · CPP page https://popl18.sigplan.org/details/CPP-2018/9/. From the abstract as reported and as summarized in *Martin-Löf à la Coq* §3 (which I read in full):

- Partiality handled by "a **graph-based variant of the Bove-Capretta method** to encode mutually recursive evaluation functions with nested recursive calls" — i.e. the same inductive-graph approach.
- Completeness "uses the **PER-model** of dependent types … formalized by relying on **impredicativity of Coq** rather than on the commonly used induction-recursion scheme which is not available in Coq."
- Adjedj et al. §3 add a caveat about scope: "types in this setting … For their normalization proof, Wieczorek et al. model types as **proof-irrelevant partial equivalence relations (PERs)**" and note (§3) that theirs is "designed to be run after extraction (which erases the complex termination argument), but not a type checker."

### 2.5 Danielsson, *Operational Semantics Using the Partiality Monad*, ICFP 2012

PDF: https://www.cse.chalmers.se/~nad/publications/danielsson-semantics-partiality-monad.pdf · DOI https://dl.acm.org/doi/10.1145/2364527.2364546. Abstract:

> "The operational semantics of a partial, functional language is often given as a relation rather than as a function. The latter approach is arguably more natural: if the language is functional, why not take advantage of this when defining the semantics? One can immediately see that **a functional semantics is deterministic** and, in a constructive setting, computable.
> This paper shows how one can use the **coinductive partiality monad** to define big-step or small-step operational semantics for lambda-calculi and virtual machines as **total, computable functions (total definitional interpreters)**."

§1 gives the motivation that matters here: an inductive big-step relation "provides no way to distinguish terms which go wrong from terms which fail to terminate" (citing Leroy & Grall 2009); recovering that distinction relationally requires a *second*, coinductive relation `ρ ⊢ t ⇑`.

**Relevance to fuel-vs-coinduction for you:** the delay monad buys you (i) determinism *for free* (it is a function), and (ii) the ability to *state* divergence. A fuel-indexed function gives you (i) for free as well — `eval fuel t ρ` is a function — which is a genuine advantage over the inductive-graph route, where determinism must be proved. What fuel does *not* give you is a clean notion of "diverges" (only "not enough fuel at this budget"), and it forces monotonicity/fuel-independence lemmas that the delay monad and the graph relation both avoid. I found **no** published dependently-typed NbE metatheory that puts the delay monad into the logical relation; Danielsson's paper is about λ-calculi and VMs with type soundness and compiler correctness, not dependent-type normalization.

### 2.6 Adjacent data points on fuel in verified kernels

- **MetaCoq.** https://metacoq.github.io/v1.2-8.16/MetaCoq.SafeChecker.PCUICSafeReduce.html header: *"We implement the reduction machine of Coq **without relying on fuel**. Instead we assume strong normalization of the system (for well-typed terms) and proceed by well-founded induction."* The fuel-based MetaCoq checker exists but, per the project's own description surfaced in search, is the *unverified* one. So: MetaCoq deliberately moved fuel *out* of the verified artifact.
- **Lean4Lean** (Carneiro), https://arxiv.org/pdf/2403.14064 — the closest analogue to Lech's setting, and it goes the *other* way. §3.2.1:
  > "It is unlikely that we can prove termination of a typechecker for Lean in Lean… we are up against Gödel's incompleteness theorem… Besides this, **the Lean type theory is known not to terminate**. Coquand and Abel constructed a counterexample to strong normalization using reduction of proofs, and this can be shown to impact definitional equality checks even for regular types… So we use what is arguably the standard solution for defining partial functions in a language like Lean or Rocq: **use a fuel parameter**, a natural number which counts the number of nested recursive calls to one of the `Methods`, and throw a `deepRecursion` error if we run out of fuel."
  
  And crucially, the specification style: *"whnf `e` returns the WHNF of `e`. From a modeling perspective, **the main important property is that if it returns `e′` and `e` is well-typed then `Γ ⊢ e ≡ e′` is provable**."* — i.e. **soundness-only, conditioned on returning**. Fuel exhaustion is simply "did not return", and no lemma ever needs a convergence premise because every lemma is already gated on a successful return. A footnote explicitly rejects Bove–Capretta here: *"we do not want to use this as the kernel API is fixed to match Lean's actual kernel function, and we also actually want it to time out on extreme cases."*

---

## TOPIC 3 — The design question, answered per project

**Question:** in published mechanized dependent-type NbE/conversion verifications, is convergence (a) baked into the logical relation, or (b) supplied as side premises?

**Answer: overwhelmingly (a). I found no project that carries convergence as free-floating side premises on transitivity or uniqueness lemmas.** Per project:

| Project | Evaluation/reduction representation | Convergence in the LR | Determinism needed? | LR indexed by |
|---|---|---|---|---|
| Abel, Habilitation 2013 | partial applicative structure (partial function); inductive graph `↘` when type-theoretic | **Baked in.** `[[t]](ρ) ∈ B :⟺ ∃b ∈ B. [[t]](ρ) ↘ b` (§3.3, p. 22); `A → B = {f | ∀a∈A. ∃b∈B. f·a ↘ b}` | Not stated — evaluation is a partial *function* by definition, so functionality is definitional | semantic type **codes** `A ∈ Set_k` with `El_k` (IR); LR by induction on `A ∈ Set_k` (§4.7) |
| Abel/Coquand/Dybjer, LICS 2007 | total combinatory algebra; `[ ] : D ⇀ Rel(D)` as an inductively defined **graph** | Baked in (PERs on values) | Functionality of `[ ]` is a **proved** lemma ("if `X = X' ∈ U` then `[X]`, `[X']` are well-defined and equal PERs"), using injectivity of code constructors | type **codes** `U`/`Type` + extension `[ ]` |
| Abel/Vezzosi/Winterhalter, ICFP 2017 | weak head evaluation relation | Baked in: `n = n' ∈ Ne :⟺ Rᵏ n ↘ m ∧ Rᵏ n' ↘ m' ∧ …` | **Yes** — "since weak head evaluation is deterministic" | PERs on values; `T ⊏∼ S` shape-approximation relation |
| Abel/Öhman/Vezzosi, POPL 2018 (Agda) | typed weak-head reduction **relation** | **Baked in.** "defining the judgements on weak head normal forms and closing them under weak head expansion"; every clause is `∃ t̄. Γ ⊢ t ⟶* t̄ ∧ …` | **Yes, explicitly** — Lemma 2.5 cited in the proofs of 3.3, 3.5, 3.7, 3.8, **3.9 (Transitivity)** | reducibility **derivation** `T :: Γ ⊩ℓ A` + level `ℓ` (induction-recursion); proved irrelevant a posteriori (3.5) |
| Adjedj et al., CPP 2024 (Coq) | same deterministic weak-head reduction relation | Baked in (same clauses) | Yes (inherited) | `LR ℓ Γ A P` — level × ctx × type × induced predicate (**small** IR) |
| McTT, ICFP 2025 (Rocq) | inductive big-step **graph** `⟦M⟧ρ ↘ m` (no fuel) | **Baked in** at judgment boundaries (`rel_mod_eval`, `rel_mod_app`, `rel_exp`, `glu_rel_exp_with_sub`); **∀-hypothesis** form inside gluing structural clauses | **Yes** — `functional_eval` + `functional_eval_rewrite_clear` used in `per_univ_elem_right_irrel` (code-uniqueness) and in all PER instances | type **values (codes)** `a` + induced relation: `DF a ≈ a' ∈ per_univ_elem i ↘ R`; gluing: `DG a ∈ glu_univ_elem i ↘ P ↘ El` |
| Wieczorek/Biernacki, CPP 2018 (Coq) | Bove–Capretta graph | PER model on values (baked in) | not verified by me | impredicative encoding instead of IR |
| MetaCoq SafeChecker | fuel-free; well-founded induction under a normalization assumption | n/a (no LR; assumes SN) | — | — |
| Lean4Lean | **fuel** (fixed 1000), `deepRecursion` error | n/a — spec is *"if it returns `e′` … then `Γ ⊢ e ≡ e′`"* | — | — |

### The dominant pattern, stated as a rule

1. **Convergence is a *property of the relation*, never a hypothesis dragged along.** Whether via `∃ v. t ⟶* v ∧ P(v)` (AÖV, Adjedj et al.) or `∃ a. ⟦t⟧ρ ↘ a ∧ (a,a') ∈ A` (Abel, McTT), the semantic judgment *asserts* convergence. Downstream lemmas therefore never need convergence premises: they *extract* convergence from the relation. Normalization ends up as a **corollary of the fundamental theorem** (AÖV Thm 3.28), not an assumption.

2. **What *is* needed as an external lemma is not convergence but *functionality/determinism* of the evaluation relation.** This is the recurring hidden cost of the ∃-style relation: two derivations `⟦t⟧ρ ↘ a` and `⟦t⟧ρ ↘ a'` must be reconciled to `a = a'`, and that is exactly where transitivity, symmetry, irrelevance, and code-uniqueness all bottom out. AÖV Lemma 2.5 → 3.5/3.7/3.8/**3.9**; McTT `functional_eval` → `per_univ_elem_right_irrel`. Abel's pen-and-paper version dodges this only because he defines evaluation as a partial *function*.

3. **Fuel, where used at all, is kept strictly outside the model.** Adjedj et al. derive a fuelled implementation from an open-recursion description and note that reflexion-based use "only relies on soundness of the functions, but not on their completeness or termination". Lean4Lean's entire kernel spec is "if it returns, the judgment holds". MetaCoq moved fuel out of the verified checker entirely.

### What this suggests for your specific choice

I'll flag this as my synthesis rather than a citation. Your machine is fueled, so unlike the relational developments you have functionality *for free at fixed fuel* (`eval n t ρ` is a function) but you pay for it with fuel-monotonicity obligations instead. The literature's answer to your question is: **bake convergence into the relation** — define the relation over successful evaluation results, so `CodeConv`, transitivity, and code-uniqueness never take convergence premises. Concretely, the two shapes that have industrial-strength precedent are:

- **∃-at-the-boundary** (McTT `rel_exp`, `rel_mod_eval`; AÖV's whnf clauses): `R(t,ρ,t',ρ') :⟺ ∃ v v' n n'. eval n t ρ = some v ∧ eval n' t' ρ' = some v' ∧ v ≈ v'`. Existentially quantifying the *fuel* here is the fuel-analogue of the graph relation; you then need a fuel-monotonicity lemma to serve the role AÖV's Lemma 2.5 serves — that is your unavoidable "determinism" obligation, and it should be proved once and used via a rewrite tactic, exactly as McTT does with `functional_eval_rewrite_clear`.
- **∀-inside-structural-clauses** (McTT `glu_univ_elem_core_pi`): `∀ b, ⟦B⟧ρ↦c ↘ b → …`. Useful precisely where you'd otherwise have to *produce* a convergence witness inside a negative position.

The one option with no precedent I could find is (b): threading convergence as a premise on each transitivity/uniqueness lemma. McTT is the closest published analogue to Lech, and it explicitly does not do this.

---

## Verified facts

All of the following I read directly in the fetched source:

1. Abel's habilitation uses partial applicative structures with Kleene-equivalence axioms, and inductive graph relations `f·a ↘ b`, `[[t]](ρ) ↘ a`, `Rⁿᶠ/Rⁿᵉ ↘` when a type-theoretic formulation is wanted (§3.2, pp. 20–21). No fuel, no coinduction, no delay monad.
2. Abel bakes convergence into semantic-type membership by explicit notational definition: `[[t]](ρ) ∈ B iff ∃b ∈ B. [[t]](ρ) ↘ b`; `A → B = {f | ∀a∈A. ∃b∈B. f·a ↘ b}` (§3.3, p. 22). The candidate space `⊤`/`⊥` is likewise defined by existential readback (§3.4, p. 25).
3. Abel's PERs are relations on the value domain `D`, not on terms (§3.6, p. 27); term equality is derived by composing with evaluation (§3.6 p. 30; §4.4 p. 46).
4. The word "deterministic" does not appear in Abel's habilitation; transitivity is PER-structural because evaluation is stipulated to be a partial function.
5. Abel's model is code-indexed: `Set_k` are sets of type *codes* with extension functions `El_k`, defined by induction-recursion (§4.3, p. 45; §4.4, p. 45–46); the Kripke logical relation for dependent types is defined "by induction on type values `A ∈ Set_k`" (§4.7, p. 51); candidate spaces are "a pair of semantic types for each type code `A ∈ U`" (§4.5).
6. Abel/Coquand/Dybjer LICS 2007 define `[ ] : D ⇀ Rel(D)` by inductively defining its **graph**, and prove that equal codes in `U` yield well-defined equal PERs.
7. AÖV POPL 2018 use typed weak-head **reduction**, prove it deterministic (Lemma 2.5), define the LR on whnfs closed under weak-head expansion with existential reduces-to clauses, index it by an inductive reducibility **derivation** `T :: Γ ⊩ℓ A` via induction-recursion plus an outer WF induction on `ℓ`, prove derivation-irrelevance a posteriori (3.5), derive weak head normalization as Theorem 3.28, and cite determinism of reduction in the proof of **Transitivity (Lemma 3.9)** (and 3.3, 3.5, 3.7, 3.8).
8. AÖV parameterize the LR by a "generic equality" required to be a **PER** (Property 2) — assumption on the parameter, theorem for the relation.
9. Adjedj et al. CPP 2024 port AÖV to Coq, replace IR by **small IR** (`LR ℓ Γ A P` with `P : Term → Type`), use deterministic weak-head reduction, and keep partiality of the *checker* entirely outside the model via McBride/Winterhalter open recursion, from which "the fuelled, coinductive or graph-based realization can all be easily recovered". Fuelled execution needs only soundness.
10. McTT (ICFP 2025) represents evaluation as inductive relations `⟦M⟧ρ ↘ m` with no fuel; proves `functional_eval`; bakes convergence into `rel_mod_eval`/`rel_mod_app`/`rel_exp`/`glu_rel_exp_with_sub`; indexes the PER by type values with `DF a ≈ a' ∈ per_univ_elem i ↘ R` (WF on `i`, small-IR style); and proves code-uniqueness as `per_univ_elem_right_irrel` using `functional_eval_rewrite_clear`. Gluing structural clauses use the ∀-form `∀ b, ⟦B⟧ρ↦c ↘ b → …`.
11. Danielsson ICFP 2012 uses the coinductive partiality monad to give total definitional interpreters; his motivation includes that a functional semantics is *deterministic*, and that inductive big-step relations cannot distinguish "goes wrong" from "diverges".
12. MetaCoq's verified reduction machine is fuel-free by well-founded induction under a normalization assumption.
13. Lean4Lean uses fuel (fixed 1000) with a `deepRecursion` error, motivated by the Abel–Coquand non-termination counterexample in Lean's theory, and specifies `whnf` purely as "if it returns `e′` and `e` is well-typed then `Γ ⊢ e ≡ e′`".

## Could not verify

- **McTT's ICFP'25 paper text itself.** ACM returns 403 to my fetcher and no arXiv preprint surfaced. All McTT technical claims above come from (i) the ICFP 2025 program abstract and (ii) my direct reading of the Rocq sources on the `main` branch. The paper's artifact branch is `icfp25`; I did not diff `main` against it, so file-level details could have shifted since publication. The Zenodo artifact (https://zenodo.org/records/15712175) would settle this.
- **Wieczorek & Biernacki CPP 2018 full text.** Paywalled; my characterization (Bove–Capretta graph, proof-irrelevant PERs, impredicativity in place of IR) rests on the CPP/ACM abstract and on the related-work discussion in *Martin-Löf à la Coq* §3, which I did read in full.
- **Whether McTT's `per_univ_elem` proofs could be restructured to avoid `functional_eval`.** I observed it is used; I did not check whether it is *essential*.
- **Abel/Vezzosi/Winterhalter ICFP 2017 in depth.** I confirmed the existential-readback PER definitions and two "since weak head evaluation is deterministic" proof steps, but did not read the full semantic-type construction.
- **Abel/Coquand/Pagano specifically.** The user named "Abel/Coquand/Pagano"; the works I located and read are Abel/Coquand/Dybjer (LICS 2007) and Abel's habilitation. I did not find and read an Abel–Coquand–Pagano paper, so I make no claims about it. (Pagano co-authored with Abel and Coquand on singleton types / NbE around 2009–2011 per the habilitation's citations of "Abel et al. 2011", but I did not fetch that paper.)
- **Any project that puts *fuel* inside a logical relation for dependent types.** I searched and found none. Absence of evidence here, not evidence of absence — but the consistent pattern across five independent developments is that fuel stays in the implementation tier.
- **"Normalization by Evaluation for Non-cumulativity" (PACMPL 2025, DOI 10.1145/3747508)** appeared repeatedly in search results and is likely a further data point in this lineage, but I did not fetch it and make no claims about it.

### Sources

- [Normalization by Evaluation: Dependent Types and Impredicativity (Abel, habilitation, 2013)](https://www.cse.chalmers.se/~abela/habil.pdf)
- [Normalization by Evaluation for Martin-Löf Type Theory with Typed Equality Judgements (Abel/Coquand/Dybjer, LICS 2007)](https://www.cse.chalmers.se/~peterd/papers/NbeMLTTEqualityJudgements.pdf)
- [Normalization by Evaluation for Sized Dependent Types (Abel/Vezzosi/Winterhalter, ICFP 2017, long version)](https://www.cse.chalmers.se/~abela/icfp17-long.pdf)
- [Decidability of Conversion for Type Theory in Type Theory (Abel/Öhman/Vezzosi, POPL 2018)](https://www.cse.chalmers.se/~abela/popl18.pdf) · [DOI](https://dl.acm.org/doi/10.1145/3158111)
- [Martin-Löf à la Coq (Adjedj/Lennon-Bertrand/Maillard/Pédrot/Pujet, CPP 2024)](https://arxiv.org/pdf/2310.06376) · [DOI](https://dl.acm.org/doi/10.1145/3636501.3636951)
- [McTT: A Verified Kernel for a Proof Assistant (Jang/Gaulin/Hu/Pientka, ICFP 2025)](https://icfp25.sigplan.org/details/icfp-2025-papers/7/McTT-A-Verified-Kernel-for-a-Proof-Assistant) · [DOI](https://dl.acm.org/doi/10.1145/3747511) · [sources](https://github.com/Beluga-lang/McTT)
- [A Coq formalization of NbE for Martin-Löf type theory (Wieczorek/Biernacki, CPP 2018)](https://dl.acm.org/doi/10.1145/3167091)
- [Operational Semantics Using the Partiality Monad (Danielsson, ICFP 2012)](https://www.cse.chalmers.se/~nad/publications/danielsson-semantics-partiality-monad.pdf)
- [MetaCoq PCUICSafeReduce (fuel-free reduction machine)](https://metacoq.github.io/v1.2-8.16/MetaCoq.SafeChecker.PCUICSafeReduce.html)
- [Lean4Lean: Verifying a Typechecker for Lean, in Lean (Carneiro)](https://arxiv.org/pdf/2403.14064)