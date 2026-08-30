import Setlec.SetR.Interp2.Step2.Lit
import Setlec.SetR.Interp2.Step2.Fuel

/-!
# `CheckStep2`, the dispatch — the clause lemmas against the runs

Where the per-clause lemmas of `Step2/{Infer,WhnfCore,DefEq,Loop}.lean`
meet the checker's own case split.  One lemma per `inferBody` branch,
shaped exactly as `Bridge/Infer.lean`'s `infer_*_claimR` family, with
the conclusion in the annotated currency.

The unfolding recipe is v1's, verbatim — `rw [inferTypeCore_succ]` then
`simp only [inferBody, viewM, Expr.view, …]` — and it transfers
unchanged, because the *checker* is the same function; only what the
clause then produces differs.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level inferTypeCore inferBody
  viewM)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-- **I1 (`.sort`).**  The clause returns `.sort (.succ u)` outright,
`denote2` evaluates both levels, and the row is `sound_sort`. -/
theorem infer_sort_claim2 (m : EnvS2 V env) {d : Nat} {u : Level}
    {t : Expr} {Δa : List AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.sort u) = .ok t) :
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.sort u) = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind, Except.ok.injEq] at h
  subst h
  refine ⟨.sort (u.eval φ), .sort (u.eval φ + 1), ?_, ?_, ?_⟩
  · rw [denote2]
  · rw [denote2]; simp [Level.eval]
  · intro ρ _
    simpa [Level.eval] using sound_sort V ρ (u.eval φ)

/-- **I2 (`.fvar`).**  The leaf returns its own annotation, so the
claim needs two facts about it that `Claims2`'s hypothesis side does
not carry — see this file's closing note.  Both are taken explicitly
here, in exactly the shape a context correspondence in the annotated
currency would supply, so the clause is usable the moment one exists. -/
theorem infer_fvar_claim2 (m : EnvS2 V env) {d idx : Nat} {n : Name}
    {ty t : Expr} {Δa : List AVExpr} {Aa tya : AVExpr}
    (hi : Δa[d - 1 - idx]? = some Aa)
    (h : inferTypeCore μ env (fuel + 1) d (.fvar idx n ty) = .ok t)
    (hden : denote2 μ m.acval env φ (fuel + 1) d ty = some tya)
    (hlink : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ tya
        = interp2 V (fun j => ρ (j + (d - 1 - idx) + 1)) Aa) :
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.fvar idx n ty) = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  split at h
  · next hlt =>
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨.bvar (d - 1 - idx), tya, by rw [denote2], hden, ?_⟩
    intro ρ hρ
    refine ⟨by simp, ?_⟩
    rw [interp2_bvar, hlink ρ hρ]
    exact hρ (d - 1 - idx) Aa hi
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `bvar` is outside the fragment: the checker throws. -/
theorem infer_bvar_claim2 (m : EnvS2 V env) {d i : Nat} {t : Expr}
    {Δa : List AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.bvar i) = .ok t) :
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.bvar i) = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## STOP — the `.fvar` clause refutes `Claims2`'s hypothesis side

`Claims2` was sealed with the context correspondence reused rather than
re-invented: `CtxOkR` at the **erasures** (`Δa.map AVExpr.erase`), on
the reasoning that it is a *function* of the annotated context and so
needs no new relation.  The conclusion side never wanted more.  **The
`.fvar` clause does**, and it wants exactly two things `CtxOkR` states
only in the relational currency:

1. **definedness** — that the leaf's annotation `ty` has a `denote2`.
   `CtxOkR`'s leaf package gives `denote cval env φ d ty = some T`; the
   annotated denotation is a different function and its definedness
   does not follow;
2. **the leaf-to-entry link** — the claim needs
   `ρ k ∈ˢ interp2 ρ tya` while `Sat2` offers
   `ρ k ∈ˢ interp2 (fun j => ρ (j+k+1)) Aa`.  `CtxOkR` bridges the
   corresponding v1 gap with `∃ T', Infer … ∧ DefEq … T' T` — **a
   relational package**, and turning a `DefEq` into an `interp2`
   equality is precisely the move the step-3 map showed does not exist
   (no `VExpr → AVExpr`, so `DefEq` has no `interp2` reading).

So the erasure route is sound for the *conclusion* and insufficient for
the *hypothesis*, and the difference shows up at one clause out of
eleven.  Both facts are taken explicitly above, so `infer_fvar_claim2`
is usable the moment a supplier exists; what it needs is a **context
correspondence stated in the annotated currency** — the `CtxOk2` this
seal's predecessor declined to invent.

*Rule: a hypothesis reused from another currency is only as good as the
weakest clause that reads it.  Check the clause that reads the context,
not the ones that only pass it along.* -/

/-- **The proposed repair**, stated but *not* wired in: `Claims2`'s
statement is a sealed artifact and swapping its context hypothesis is a
junction decision, not a consumer's.

`CtxOk2` is `CtxOkR`'s leaf package transposed — per `fvar` leaf, the
annotation denotes under `denote2`, and its interpretation agrees with
the context entry read in the entry's own tail context.  The second
conjunct is where `CtxOkR`'s `∃ T', Infer … ∧ DefEq …` lived; here it
is the semantic fact directly, because that is what the consumer reads
and the relational form has no `interp2` meaning.

Substituting this for `CtxOkR (Δa.map erase)` in all four claims closes
`infer_fvar_claim2` by supplying both of its explicit hypotheses, and
touches no other clause — the other ten pass the context along without
reading it. -/
def CtxOk2 {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel d : Nat) (Δa : List AVExpr) (e : Expr) :
    Prop :=
  Δa.length = d ∧
  ∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.fvarsBelow l.1 l.2.2 ∧
    ∃ tya Aa,
      denote2 μ m.acval env φ fuel d l.2.2 = some tya ∧
      Δa[d - 1 - l.1]? = some Aa ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ tya
          = interp2 V (fun j => ρ (j + (d - 1 - l.1) + 1)) Aa

/-- `CtxOk2` supplies exactly what `infer_fvar_claim2` takes
explicitly — the repair's correctness, checked rather than asserted. -/
theorem CtxOk2.fvar_leaf {env : Env} {m : EnvS2 V env} {μ : CheckMode}
    {φ : Name → Nat} {fuel d idx : Nat} {n : Name} {ty : Expr}
    {Δa : List AVExpr}
    (hC : CtxOk2 m μ φ fuel d Δa (.fvar idx n ty)) :
    ∃ tya Aa,
      denote2 μ m.acval env φ fuel d ty = some tya ∧
      Δa[d - 1 - idx]? = some Aa ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ tya
          = interp2 V (fun j => ρ (j + (d - 1 - idx) + 1)) Aa := by
  obtain ⟨-, hleaf⟩ := hC
  obtain ⟨-, -, tya, Aa, h1, h2, h3⟩ :=
    hleaf (idx, n, ty) (by simp [Expr.fvarLeaves])
  exact ⟨tya, Aa, h1, h2, h3⟩

/-! # Re-pointed to `Claims2A` — the amended dispatch (seal 6)

Everything above is the **sealed** shape and stays as the tombstone.
Below is the same layer against `Interp2/Claims2A.lean`'s
`InferClaims2A`, whose clause obligation differs in three ways:

* the subject's annotation is a **hypothesis** at its own fuel `F`
  (R1), not something the clause produces;
* the returned type's annotation is produced at some `F' ≥ F` (R3);
* `CtxOk2` — *this file's* proposal, now wired — replaces
  `CtxOkR`-on-erasures (the seal-3 STOP below).

The three clauses here all take `F' = F`: `.sort` returns a run-free
shape and `.fvar` reads its type's annotation out of `CtxOk2` at the
claim's own `F`.  **R3's slack is not consumed at this layer** — the
`.const` clause (not ours) is where it is spent.  `μ.verified = true`
(R4) is not consumed here either: no clause of this layer denotes a
`λ`.  Both are recorded rather than assumed: an unused premise in a
statement one has re-pointed is evidence about *where* the defect
lived.
-/

section Amended

open Setlec (BinderMeta whnf whnfBody whnfLoop whnfStep whnfLoopFuel
  pureFns whnfCore)

variable {m : EnvS2 V env}

/-! ## The `CtxOk2` kit — stated by the supplier (T5)

`CtxOk2` is read by one clause (`.fvar`) and *threaded* by the other
ten and by all three of the other quarters.  Threading needs its own
lemmas, and by the T5 rule they are stated here rather than guessed at
each consumer.  Everything in this subsection is about the **leaf
package**; nothing about it depends on the claim family's shape, so it
survives any further amendment of `Claims2A`. -/

/-- The context has exactly the ambient depth. -/
theorem CtxOk2.length {F d : Nat} {Δa : List AVExpr} {e : Expr}
    (hC : CtxOk2 m μ φ F d Δa e) : Δa.length = d := hC.1

/-- **`CtxOk2` is monotone in the annotation fuel.**  The one lemma R1
and R3 make unavoidable: a clause holding the context at `F` and
needing it at `F' ≥ F` raises it here, and the leaf annotations `tya`
are *unchanged*, so every link in the package transports verbatim.
`denote2_fuelMono` (`Step2/Fuel.lean`) is a theorem, so this is one
too — there is no input to schedule. -/
theorem CtxOk2.fuelMono {F F' d : Nat} {Δa : List AVExpr} {e : Expr}
    (hle : F ≤ F') (hC : CtxOk2 m μ φ F d Δa e) :
    CtxOk2 m μ φ F' d Δa e := by
  refine ⟨hC.1, fun l hl => ?_⟩
  obtain ⟨hlt, hfb, tya, Aa, h1, h2, h3⟩ := hC.2 l hl
  exact ⟨hlt, hfb, tya, Aa, denote2_fuelMono hle d l.2.2 h1, h2, h3⟩

/-- At depth `0` there is nothing to constrain — the shape every
declaration-level statement uses.  Transpose of `CtxOkR.nil`. -/
theorem CtxOk2.nil {F : Nat} {e : Expr} (h : e.fvarLeaves = []) :
    CtxOk2 m μ φ F 0 [] e := by
  refine ⟨rfl, fun l hl => ?_⟩
  rw [h] at hl
  exact nomatch hl

/-- **Covered leaves inherit the correspondence.**  The list form;
`of_subset` below is the singleton case.  Transpose of
`CtxOkR.of_cover`. -/
theorem CtxOk2.of_cover {F d : Nat} {Δa : List AVExpr} {L : List Expr}
    {e : Expr} (hlen : Δa.length = d)
    (hL : ∀ x ∈ L, CtxOk2 m μ φ F d Δa x)
    (hsub : ∀ l ∈ e.fvarLeaves, ∃ x ∈ L, l ∈ x.fvarLeaves) :
    CtxOk2 m μ φ F d Δa e :=
  ⟨hlen, fun l hl => by
    obtain ⟨x, hx, hlx⟩ := hsub l hl
    exact (hL x hx).2 l hlx⟩

/-- Restriction along one expression: a subterm's leaves are a subset
of the whole's.  **This is the only shape the ten threading clauses
need going down**; going *up* through a binder is `CtxOk2.open`, which
is the residue at the end of this section. -/
theorem CtxOk2.of_subset {F d : Nat} {Δa : List AVExpr} {e e' : Expr}
    (hC : CtxOk2 m μ φ F d Δa e)
    (hsub : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) :
    CtxOk2 m μ φ F d Δa e' :=
  ⟨hC.1, fun l hl => hC.2 l (hsub l hl)⟩

/-- An application's leaves are its parts'.  Transpose of
`CtxOkR.app`. -/
theorem CtxOk2.app {F d : Nat} {Δa : List AVExpr} {f x : Expr}
    (hf : CtxOk2 m μ φ F d Δa f) (hx : CtxOk2 m μ φ F d Δa x) :
    CtxOk2 m μ φ F d Δa (.app f x) := by
  refine ⟨hf.1, fun l hl => ?_⟩
  rw [Expr.fvarLeaves] at hl
  rcases List.mem_append.mp hl with h | h
  · exact hf.2 l h
  · exact hx.2 l h

/-! ### The projections, one per `inferBody` branch that recurses

Each is `of_subset` at a `simp [Expr.fvarLeaves]`; they are spelled out
so a consumer never has to reopen `fvarLeaves`. -/

theorem CtxOk2.app_fn {F d : Nat} {Δa : List AVExpr} {f x : Expr}
    (hC : CtxOk2 m μ φ F d Δa (.app f x)) : CtxOk2 m μ φ F d Δa f :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem CtxOk2.app_arg {F d : Nat} {Δa : List AVExpr} {f x : Expr}
    (hC : CtxOk2 m μ φ F d Δa (.app f x)) : CtxOk2 m μ φ F d Δa x :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem CtxOk2.forallE_ty {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty body : Expr} {mb : BinderMeta}
    (hC : CtxOk2 m μ φ F d Δa (.forallE n ty body mb)) :
    CtxOk2 m μ φ F d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem CtxOk2.forallE_body {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty body : Expr} {mb : BinderMeta}
    (hC : CtxOk2 m μ φ F d Δa (.forallE n ty body mb)) :
    CtxOk2 m μ φ F d Δa body :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem CtxOk2.lam_ty {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty body : Expr} {mb : BinderMeta}
    (hC : CtxOk2 m μ φ F d Δa (.lam n ty body mb)) :
    CtxOk2 m μ φ F d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem CtxOk2.lam_body {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty body : Expr} {mb : BinderMeta}
    (hC : CtxOk2 m μ φ F d Δa (.lam n ty body mb)) :
    CtxOk2 m μ φ F d Δa body :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem CtxOk2.letE_ty {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty val body : Expr}
    (hC : CtxOk2 m μ φ F d Δa (.letE n ty val body)) :
    CtxOk2 m μ φ F d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]
    exact List.mem_append_left _ (List.mem_append_left _ hl)

theorem CtxOk2.letE_val {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty val body : Expr}
    (hC : CtxOk2 m μ φ F d Δa (.letE n ty val body)) :
    CtxOk2 m μ φ F d Δa val :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]
    exact List.mem_append_left _ (List.mem_append_right _ hl)

theorem CtxOk2.letE_body {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty val body : Expr}
    (hC : CtxOk2 m μ φ F d Δa (.letE n ty val body)) :
    CtxOk2 m μ φ F d Δa body :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem CtxOk2.proj_arg {F d : Nat} {Δa : List AVExpr} {sn : Name}
    {i : Nat} {e : Expr}
    (hC : CtxOk2 m μ φ F d Δa (.proj sn i e)) :
    CtxOk2 m μ φ F d Δa e :=
  hC.of_subset fun _ hl => by rw [Expr.fvarLeaves]; exact hl

/-- A leaf's *annotation* is itself covered — the package is
hereditary through `fvarLeaves`, which recurses into the type. -/
theorem CtxOk2.fvar_ty {F d idx : Nat} {Δa : List AVExpr} {n : Name}
    {ty : Expr} (hC : CtxOk2 m μ φ F d Δa (.fvar idx n ty)) :
    CtxOk2 m μ φ F d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_cons_of_mem _ hl

/-! ## The smallest-fuel test, applied to `CtxOk2` itself

The rule earned at seal 6 — *a statement that quantifies a fuel must
be checked at the smallest fuel it admits* — turned on this file's own
proposal, since three quarters are about to build on it.

The answer is: **`CtxOk2` is empty at `F = 1` for any subject carrying
a binder-typed leaf**, by exactly the argument that killed `EnvS2`'s
`acval_defn`.  And that is *safe*, unlike `EnvS2`'s, for one structural
reason: `CtxOk2` is a **hypothesis** of `InferClaims2A`, not a field
anybody has to build.  An empty hypothesis makes the claim vacuous at
that fuel; it does not make it false.  Together with `CtxOk2.fuelMono`
and `denote2_fuelMono` a consumer is free to raise `F` until the
context is inhabited, and R3's `F ≤ F'` is what lets the conclusion
follow it up.

*Rule (the converse of the `EnvS2` one): the smallest-fuel test is
about which* side *of the arrow a success-demanding equation sits on.
On the hypothesis side, unsatisfiability at low fuel is vacuity; on the
conclusion or field side it is falsity.* -/

/-- At fuel `1` the reduction loop cannot take its first step —
`Step2/Whnf.lean`'s `whnf_one_error` and `Step2/InferQ.lean`'s
`whnf_one_not_ok`, re-derived here because both live *downstream* of
this file. -/
private theorem whnf_one_errorD (d : Nat) (t : Expr) :
    whnf μ env 1 d t
      = .error (.internal "fuel exhausted: whnfCore") := by
  obtain ⟨n, hn⟩ := Setlec.whnfLoopFuel_succ
  rw [Setlec.whnf_succ, whnfBody, hn, whnfLoop, whnfStep]
  simp [Setlec.whnfCore_def, Setlec.whnfCore_zero, throw, throwThe,
    MonadExceptOf.throw, Bind.bind, Except.bind]

private theorem sortOfE_oneD (d : Nat) (e : Expr) :
    sortOfE μ env φ 1 d e = none := by
  rw [sortOfE]
  cases (inferTypeCore μ env 1 d e).toOption with
  | none => rfl
  | some t => simp [whnf_one_errorD, Except.toOption]

/-- **The negative half, mechanized**: no context whose subject has a
`∀`-typed leaf satisfies `CtxOk2` at fuel `1`.  A variable of function
type is the commonest thing there is, so this is not a corner. -/
theorem ctxOk2_one_forallE_leaf_false {d idx : Nat} {n nb : Name}
    {tyb bodyb : Expr} {mb : BinderMeta} {Δa : List AVExpr}
    (hC : CtxOk2 m μ φ 1 d Δa
      (.fvar idx n (.forallE nb tyb bodyb mb))) : False := by
  obtain ⟨tya, -, hden, -, -⟩ := CtxOk2.fvar_leaf hC
  rw [denote2] at hden
  rcases hta : denote2 μ m.acval env φ 1 d tyb with _ | ta
  · rw [hta] at hden; exact nomatch hden
  rw [hta] at hden
  rcases hba : denote2 μ m.acval env φ 1 (d + 1)
      (bodyb.instantiate1 (.fvar d nb tyb)) with _ | ba
  · rw [hba] at hden; exact nomatch hden
  rw [hba, sortOfE_oneD] at hden
  exact nomatch hden

/-- **The positive half**: at depth `0` the hypothesis is inhabited at
*every* fuel, which is what keeps the vacuity from being global — the
declaration-level entry point never loses anything. -/
theorem ctxOk2_zero_inhabited {F : Nat} {e : Expr}
    (h : e.fvarLeaves = []) : CtxOk2 m μ φ F 0 [] e :=
  CtxOk2.nil h

/-! ## The clauses, re-pointed -/

/-- **I1A (`.sort`), amended.**  `.sort` is the run-free clause: the
subject's annotation is forced by `denote2`'s first equation and the
returned type's is `Level.eval`'s successor, so `F' = F` and neither
R3's slack nor R4's `μ.verified` is consumed.  R1 makes this clause
*easier* than its sealed form — the annotation is handed over instead
of being exhibited. -/
theorem infer_sort_claim2A {d : Nat} {u : Level} {t : Expr}
    {Δa : List AVExpr} {F : Nat} {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.sort u) = .ok t)
    (hea : denote2 μ m.acval env φ F d (.sort u) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind, Except.ok.injEq] at h
  subst h
  rw [denote2] at hea
  obtain rfl : ea = .sort (u.eval φ) := (Option.some.inj hea).symm
  refine ⟨F, .sort (u.eval φ + 1), Nat.le_refl F, ?_, ?_⟩
  · rw [denote2]; simp [Level.eval]
  · intro ρ _
    simpa [Level.eval] using sound_sort V ρ (u.eval φ)

/-- **I2A (`.fvar`), amended — the clause that was BLOCKED.**

The seal-3 STOP above is discharged: the two facts `infer_fvar_claim2`
had to take explicitly are now *derived*, from `CtxOk2` via
`CtxOk2.fvar_leaf`, which is what `InferClaims2A` hands the clause.
Nothing else moved.

Two things are worth recording because they were not obvious before
the amendment landed.  First, `CtxOk2` is read at the claim's **own**
`F`, and the leaf's annotation it produces is at that same `F`, so
`F' = F`: the `.fvar` clause does not spend R3's slack even though it
is one of the two witnesses that *forced* R3.  R3 was needed for
`.const`, whose returned type comes from the environment rather than
from a hypothesis about the context.  Second, `denote2` of the subject
gives nothing here — its `.fvar` equation returns `.bvar (d-1-idx)`
**without recursing into the annotation** — which is precisely why the
definedness of `ty`'s annotation had to come from the context and could
not be read off the subject. -/
theorem infer_fvar_claim2A {d idx : Nat} {n : Name} {ty t : Expr}
    {Δa : List AVExpr} {F : Nat} {ea : AVExpr}
    (hC : CtxOk2 m μ φ F d Δa (.fvar idx n ty))
    (h : inferTypeCore μ env (fuel + 1) d (.fvar idx n ty) = .ok t)
    (hea : denote2 μ m.acval env φ F d (.fvar idx n ty) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tya, Aa, hden, hi, hlink⟩ := CtxOk2.fvar_leaf hC
  rw [denote2] at hea
  obtain rfl : ea = .bvar (d - 1 - idx) := (Option.some.inj hea).symm
  rw [Setlec.inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    refine ⟨F, tya, Nat.le_refl F, hden, ?_⟩
    intro ρ hρ
    refine ⟨by simp, ?_⟩
    rw [interp2_bvar, hlink ρ hρ]
    exact hρ (d - 1 - idx) Aa hi
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **I3A (`.bvar`), amended.**  Outside the fragment: the checker
throws, so the clause is vacuous at every fuel and every `F`. -/
theorem infer_bvar_claim2A {d i : Nat} {t : Expr}
    {Δa : List AVExpr} {F : Nat} {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.bvar i) = .ok t)
    (_hea : denote2 μ m.acval env φ F d (.bvar i) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

end Amended

end Setlec.SetR.Interp2