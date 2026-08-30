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

/-- `CtxOk2.fuelMono` under the name the other quarters were promised.
Kept as a separate declaration rather than a rename because the sealed
name is already cited in this file's prose; they are the same
theorem. -/
theorem CtxOk2.mono {F F' d : Nat} {Δa : List AVExpr} {e : Expr}
    (hle : F ≤ F') (h : CtxOk2 m μ φ F d Δa e) :
    CtxOk2 m μ φ F' d Δa e :=
  CtxOk2.fuelMono hle h

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

/-! ## Threading through a binder — `denote2`'s depth shift

The ten clauses that do not read the context still have to *extend* it:
the `.forallE`/`.lam`/`.letE` branches call the claim at `d + 1` over
`Aa :: Δa` on `body.instantiate1 (.fvar d n ty)`.  `CtxOkR` has this as
`CtxOkR.open`; `CtxOk2` needs the same, and the step it needs is
**`denote2`'s depth shift** — the exact analogue of
`denote_weaken_top` (`Setlec/Verify/Denote/Shift.lean`).

It did not exist, and there was a reason to fear it could not: `denote`
depends on the depth only through its `fvar` clause, while `denote2`
also calls `sortOfE`/`lamSortE`, i.e. the **checker** at that depth.
So the annotated shift needs the checker to be depth-stable, which is
a much larger fact than anything on the `denote` side.

It is available.  `Setlec.shiftClaims` (`Setlec/Verify/Deep.lean`) is
exactly the bisimulation — a run at depth `d` on `e` against the run at
depth `d + 1` on `e.shiftFrom p` — landed for the memo cache's
depth-free keys.  The two lemmas below are its `sortOfE`/`lamSortE`
corollaries, and `denote2_shiftFrom` is then `denote_shiftFrom`'s
recursion with those two rewrites added at the binder clauses.

*Finding: the annotated lane's depth shift costs nothing new — the
checker half was paid for by the cache and the sort computations sit
directly on it.  The one genuinely new premise is on the valuation
(`hacl` below), and it is `denote_shiftFrom`'s `hcl` transposed.* -/

variable {acval : Name → (Name → Nat) → AVExpr}

/-- `sortOfE` is depth-stable under the fvar shift: the run is
(`shiftClaims`), and a `.sort` is its own shift. -/
theorem sortOfE_shiftFrom (henv : Setlec.EnvWF env) {f p d : Nat}
    (hpd : p ≤ d) {e : Expr} (hw : Expr.WScoped d e) :
    sortOfE μ env φ f (d + 1) (e.shiftFrom p)
      = sortOfE μ env φ f d e := by
  have hI := (Setlec.shiftClaims (mode := μ) henv f).infer hpd hw
  unfold sortOfE
  rw [hI]
  cases hi : inferTypeCore μ env f d e with
  | error err => rfl
  | ok t =>
    have hwt : Expr.WScoped d t :=
      Setlec.inferTypeCore_WScoped henv f hi hw
    have hW := (Setlec.shiftClaims (mode := μ) henv f).whnf hpd hwt
    simp only [Except.toOption, Except.map]
    rw [hW]
    cases hwh : whnf μ env f d t with
    | error err => rfl
    | ok w =>
      simp only [Except.map]
      cases w <;> try rfl
      · next idx nm ty' =>
        have hfv : Expr.shiftFrom p (.fvar idx nm ty')
            = .fvar (if idx ≥ p then idx + 1 else idx) nm
              (if idx ≥ p then Expr.shiftFrom p ty' else ty') := by
          simp only [Setlec.Expr.shiftFrom]; split <;> rfl
        rw [hfv]

/-- `lamSortE` is depth-stable: an inference then a `sortOfE`. -/
theorem lamSortE_shiftFrom (henv : Setlec.EnvWF env) {f p d : Nat}
    (hpd : p ≤ d) {e : Expr} (hw : Expr.WScoped d e) :
    lamSortE μ env φ f (d + 1) (e.shiftFrom p)
      = lamSortE μ env φ f d e := by
  have hI := (Setlec.shiftClaims (mode := μ) henv f).infer hpd hw
  unfold lamSortE
  rw [hI]
  cases hi : inferTypeCore μ env f d e with
  | error err => rfl
  | ok t =>
    have hwt : Expr.WScoped d t :=
      Setlec.inferTypeCore_WScoped henv f hi hw
    simp only [Except.toOption, Except.map]
    exact sortOfE_shiftFrom henv hpd hwt

/-- The `Nat`-literal spine is lift-invariant when its two heads
are. -/
private theorem natLitT2_liftN {za sa : AVExpr} {k : Nat}
    (hz : za.liftN 1 k = za) (hs : sa.liftN 1 k = sa) :
    ∀ n : Nat, (natLitT2 za sa n).liftN 1 k = natLitT2 za sa n := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih =>
    show (AVExpr.app sa (natLitT2 za sa n)).liftN 1 k = _
    rw [AVExpr.liftN_app, hs, ih]
    rfl

/-- Ditto the character-list spine. -/
private theorem charListT2_liftN {nilA consA ofNatA za sa : AVExpr}
    {k : Nat} (hn : nilA.liftN 1 k = nilA)
    (hc : consA.liftN 1 k = consA) (ho : ofNatA.liftN 1 k = ofNatA)
    (hz : za.liftN 1 k = za) (hs : sa.liftN 1 k = sa) :
    ∀ cs : List Char,
      (charListT2 nilA consA ofNatA za sa cs).liftN 1 k
        = charListT2 nilA consA ofNatA za sa cs := by
  intro cs
  induction cs with
  | nil => exact hn
  | cons c cs ih =>
    show (AVExpr.app (.app consA (.app ofNatA _)) _).liftN 1 k = _
    rw [AVExpr.liftN_app, AVExpr.liftN_app, AVExpr.liftN_app, hc, ho,
      natLitT2_liftN hz hs, ih]
    rfl

/-- **`denote2`'s depth shift.**  `denote_shiftFrom`'s recursion
(`Setlec/Verify/Denote/Shift.lean`) with the two sort computations
rewritten by `sortOfE_shiftFrom`/`lamSortE_shiftFrom`.

Generalized over the *cut* `p` for the same reason v1 is: the binder
clause compares `denote2 (d+2) (body.instantiate1 (.fvar (d+1) …))`
with `denote2 (d+1) (body.instantiate1 (.fvar d …))`, two genuinely
different expressions, related by `Expr.shiftFrom d`.

`hacl` is `denote_shiftFrom`'s `hcl` transposed: the stored annotated
leaves must be lift-invariant.  It is an explicit premise, not an
`EnvS2` field, because `EnvS2` has none — see the supplier note after
`CtxOk2.open`. -/
theorem denote2_shiftFrom (henv : Setlec.EnvWF env)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ) {f p : Nat} :
    ∀ (e : Expr) (d : Nat), p ≤ d → Expr.WScoped d e →
      denote2 μ acval env φ f (d + 1) (e.shiftFrom p) =
        (denote2 μ acval env φ f d e).map (AVExpr.liftN 1 · (d - p))
  | .bvar i, d, _, _ => by
    have h1 : denote2 μ acval env φ f (d + 1) (.bvar i) = none := by
      rw [denote2.eq_def]
    have h2 : denote2 μ acval env φ f d (.bvar i) = none := by
      rw [denote2.eq_def]
    simp [Setlec.Expr.shiftFrom, h1, h2]
  | .sort u, d, _, _ => by
    simp only [Setlec.Expr.shiftFrom, denote2, Option.map_some]
    rfl
  | .const n us, d, _, _ => by
    simp only [Setlec.Expr.shiftFrom, denote2]
    cases env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      split
      · simp only [Option.map_some, hacl]
      · rfl
  | .fvar idx n ty, d, hpd, hw => by
    rw [Setlec.Expr.WScoped] at hw
    have hlt : idx < d := hw.1
    simp only [Setlec.Expr.shiftFrom]
    split
    · next hge =>
      rw [denote2, denote2, Option.map_some, AVExpr.liftN_bvar,
        if_pos (show d - 1 - idx < d - p by omega),
        show d + 1 - 1 - (idx + 1) = d - 1 - idx from by omega]
    · next hge =>
      rw [denote2, denote2, Option.map_some, AVExpr.liftN_bvar,
        if_neg (show ¬ d - 1 - idx < d - p by omega),
        show d + 1 - 1 - idx = d - 1 - idx + 1 from by omega]
  | .app fe a, d, hpd, hw => by
    rw [Setlec.Expr.WScoped] at hw
    simp only [Setlec.Expr.shiftFrom, denote2]
    rw [denote2_shiftFrom henv hacl fe d hpd hw.1,
      denote2_shiftFrom henv hacl a d hpd hw.2]
    cases denote2 μ acval env φ f d fe <;>
      cases denote2 μ acval env φ f d a <;> rfl
  | .forallE n ty body mb, d, hpd, hw => by
    rw [Setlec.Expr.WScoped] at hw
    have hwb : Expr.WScoped (d + 1)
        (body.instantiate1 (.fvar d n ty)) :=
      Setlec.Expr.WScoped.instantiate1 hw.1 0 hw.2
    simp only [Setlec.Expr.shiftFrom, denote2]
    rw [← Setlec.Expr.shiftFrom_instantiate1 hpd body 0,
      denote2_shiftFrom henv hacl ty d hpd hw.1,
      denote2_shiftFrom henv hacl (body.instantiate1 (.fvar d n ty))
        (d + 1) (by omega) hwb,
      sortOfE_shiftFrom henv hpd hw.1,
      sortOfE_shiftFrom (p := p) henv (by omega) hwb,
      show d + 1 - p = d - p + 1 from by omega]
    cases denote2 μ acval env φ f d ty with
    | none => rfl
    | some ta =>
      cases denote2 μ acval env φ f (d + 1)
          (body.instantiate1 (.fvar d n ty)) with
      | none => rfl
      | some ba =>
        cases sortOfE μ env φ f d ty with
        | none => rfl
        | some u =>
          cases sortOfE μ env φ f (d + 1)
              (body.instantiate1 (.fvar d n ty)) with
          | none => rfl
          | some v => rfl
  | .lam n ty body mb, d, hpd, hw => by
    rw [Setlec.Expr.WScoped] at hw
    have hwb : Expr.WScoped (d + 1)
        (body.instantiate1 (.fvar d n ty)) :=
      Setlec.Expr.WScoped.instantiate1 hw.1 0 hw.2
    simp only [Setlec.Expr.shiftFrom, denote2]
    rw [← Setlec.Expr.shiftFrom_instantiate1 hpd body 0,
      denote2_shiftFrom henv hacl ty d hpd hw.1,
      denote2_shiftFrom henv hacl (body.instantiate1 (.fvar d n ty))
        (d + 1) (by omega) hwb,
      lamSortE_shiftFrom (p := p) henv (by omega) hwb,
      show d + 1 - p = d - p + 1 from by omega]
    cases denote2 μ acval env φ f d ty with
    | none => rfl
    | some ta =>
      cases denote2 μ acval env φ f (d + 1)
          (body.instantiate1 (.fvar d n ty)) with
      | none => rfl
      | some ba =>
        cases lamSortE μ env φ f (d + 1)
            (body.instantiate1 (.fvar d n ty)) with
        | none => rfl
        | some v => rfl
  | .letE n ty val body, d, hpd, hw => by
    rw [Setlec.Expr.WScoped] at hw
    have hwb : Expr.WScoped (d + 1)
        (body.instantiate1 (.fvar d n ty)) :=
      Setlec.Expr.WScoped.instantiate1 hw.1 0 hw.2.2
    simp only [Setlec.Expr.shiftFrom, denote2]
    rw [← Setlec.Expr.shiftFrom_instantiate1 hpd body 0,
      denote2_shiftFrom henv hacl ty d hpd hw.1,
      denote2_shiftFrom henv hacl val d hpd hw.2.1,
      denote2_shiftFrom henv hacl (body.instantiate1 (.fvar d n ty))
        (d + 1) (by omega) hwb,
      show d + 1 - p = d - p + 1 from by omega]
    cases denote2 μ acval env φ f d ty with
    | none => rfl
    | some ta =>
      cases denote2 μ acval env φ f d val with
      | none => rfl
      | some va =>
        cases denote2 μ acval env φ f (d + 1)
            (body.instantiate1 (.fvar d n ty)) with
        | none => rfl
        | some ba => rfl
  | .proj sn i e, d, hpd, hw => by
    rw [Setlec.Expr.WScoped] at hw
    simp only [Setlec.Expr.shiftFrom, denote2]
    rw [denote2_shiftFrom henv hacl e d hpd hw]
    cases denote2 μ acval env φ f d e with
    | none => rfl
    | some ea =>
      simp only [Option.map_some]
      split
      · rfl
      · rfl
  | .lit (.natVal k), d, _, _ => by
    simp only [Setlec.Expr.shiftFrom, denote2]
    split
    · simp only [Option.map_some]
      rw [natLitT2_liftN (hacl _ _ _) (hacl _ _ _)]
    · rfl
  | .lit (.strVal s), d, _, _ => by
    simp only [Setlec.Expr.shiftFrom, denote2]
    split
    · simp only [Option.map_some]
      refine congrArg some ?_
      symm
      rw [AVExpr.liftN_app, hacl,
        charListT2_liftN (by rw [AVExpr.liftN_app, hacl, hacl])
          (by rw [AVExpr.liftN_app, hacl, hacl]) (hacl _ _ _)
          (hacl _ _ _) (hacl _ _ _)]
    · rfl
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Setlec.Expr.sizeB]; omega)
  | (rw [Setlec.Expr.sizeB_instantiate1 _ rfl]
     simp [Setlec.Expr.sizeB]; omega)
  | (simp [Setlec.Expr.sizeB])

/-- **One level of weakening.**  `denote_weaken_top`'s transpose: a
`d`-scoped term denoted at `d + 1` is its depth-`d` annotation,
lifted. -/
theorem denote2_weaken_top (henv : Setlec.EnvWF env)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ) {f d : Nat} {e : Expr}
    (hw : Expr.WScoped d e) :
    denote2 μ acval env φ f (d + 1) e
      = (denote2 μ acval env φ f d e).map (AVExpr.liftN 1 · 0) := by
  have h := denote2_shiftFrom (μ := μ) (φ := φ) (f := f) henv hacl
    (p := d) e d (Nat.le_refl d) hw
  rw [Setlec.Expr.shiftFrom_eq_self hw.fvarsBelow, Nat.sub_self] at h
  exact h

/-- The tail of a satisfying valuation satisfies the tail context —
`Sat2_cons`'s inverse, and what every weakening step consumes. -/
theorem Sat2_tail {Δa : List AVExpr} {Ba : AVExpr} {ρ : Nat → V}
    (hρ : Sat2 V (Ba :: Δa) ρ) : Sat2 V Δa (fun j => ρ (j + 1)) := by
  intro i Aa hi
  exact hρ (i + 1) Aa (by simpa using hi)

/-- **Weakening the context correspondence by one binder.**  Every
leaf of an already-scoped subject survives one more binder: its
annotation lifts (`denote2_weaken_top`), its slot moves up by the new
head, and `Sat2_tail` carries the link.  Transpose of
`CtxOkR.weakenTop`. -/
theorem CtxOk2.weakenTop (henv : Setlec.EnvWF env)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (m.acval n ψ).liftN 1 k = m.acval n ψ)
    {F d : Nat} {Δa : List AVExpr} {Ba : AVExpr} {e : Expr}
    (hw : Expr.WScoped d e) (hC : CtxOk2 m μ φ F d Δa e) :
    CtxOk2 m μ φ F (d + 1) (Ba :: Δa) e := by
  refine ⟨by simp [hC.1], fun l hl => ?_⟩
  obtain ⟨hlt, hfb, tya, Aa, hden, hi, hlink⟩ := hC.2 l hl
  have hwl : Expr.WScoped d l.2.2 :=
    (Setlec.Expr.WScoped_leaves e hw l hl).2.mono (by omega)
  refine ⟨by omega, hfb, tya.liftN 1 0, Aa, ?_, ?_, ?_⟩
  · rw [denote2_weaken_top henv hacl hwl, hden]
    rfl
  · rw [show d + 1 - 1 - l.1 = (d - 1 - l.1) + 1 from by omega]
    simpa using hi
  · intro ρ hρ
    rw [show d + 1 - 1 - l.1 = d - 1 - l.1 + 1 from by omega,
      show AVExpr.liftN 1 tya 0 = tya.lift from rfl,
      interp2_lift (V := V) tya ρ, hlink _ (Sat2_tail hρ)]
    congr 1

/-- **Opening a binder extends the context correspondence.**  The new
head of `Δa` is the binder's own annotation, so the new leaf's package
is `denote2_weaken_top` plus `interp2_lift` — `Sat2`'s tail convention
matches the lift exactly, with no index arithmetic left over.
Transpose of `CtxOkR.open`, and the lemma the `.forallE`/`.lam`/`.letE`
clauses of every quarter need to reach their recursive call. -/
theorem CtxOk2.open (henv : Setlec.EnvWF env)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (m.acval n ψ).liftN 1 k = m.acval n ψ)
    {F d : Nat} {Δa : List AVExpr} {body ty : Expr} {n : Name}
    {ta : AVExpr}
    (hb : CtxOk2 m μ φ F d Δa body) (ht : CtxOk2 m μ φ F d Δa ty)
    (hwb : Expr.WScoped d body) (hwt : Expr.WScoped d ty)
    (hty : denote2 μ m.acval env φ F d ty = some ta) :
    CtxOk2 m μ φ F (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d n ty)) := by
  refine ⟨by simp [hb.1], fun l hl => ?_⟩
  rcases Setlec.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
  · exact (CtxOk2.weakenTop (Ba := ta) henv hacl hwb hb).2 l hl'
  · rw [Setlec.Expr.fvarLeaves] at hl'
    rcases List.mem_cons.mp hl' with rfl | hl''
    · refine ⟨by omega, hwt.fvarsBelow, ta.liftN 1 0, ta, ?_, ?_, ?_⟩
      · rw [denote2_weaken_top henv hacl hwt, hty]
        rfl
      · rw [show d + 1 - 1 - d = 0 from by omega]
        rfl
      · intro ρ _
        show interp2 V ρ (AVExpr.liftN 1 ta 0)
          = interp2 V (fun j => ρ (j + (d + 1 - 1 - d) + 1)) ta
        rw [show d + 1 - 1 - d = 0 from by omega,
          show AVExpr.liftN 1 ta 0 = ta.lift from rfl,
          interp2_lift (V := V) ta ρ]
    · exact (CtxOk2.weakenTop (Ba := ta) henv hacl hwt ht).2 l hl''

/-! ### Supplier note: `hacl` wants to be an `EnvS2` field

`denote2_shiftFrom` and everything above it carry
`hacl : ∀ n ψ k, (acval n ψ).liftN 1 k = acval n ψ` as an explicit
premise.  That is `denote_shiftFrom`'s `hcl : ∀ n ψ, VExpr.Closed
(cval n ψ)` transposed, and it is taken the same way v1 takes it — at
the consumer, not from the structure — because **`EnvS2` has no
closedness field for `acval` and `AVExpr` has no `Closed` predicate**.

It is discharged for `EnvS2.empty` by `rfl` (`acval = .const .empty
[0]`), and it is a *syntactic* condition on an install-fixed object, so
unlike the fields STOP 2 refuted it carries no fuel and cannot go false
at a small one.  If `EnvS2` is being reshaped anyway, this is the field
to add; until then every consumer of `CtxOk2.open` passes it along. -/

end Amended

end Setlec.SetR.Interp2