import Setlec.SetR.Annot.EnvS2U
import Setlec.SetBase.LitStep2
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

## THE KIT INVENTORY — check here before writing a helper

This file is the **supplier** for every quarter. Seven times in this
campaign two quarters wrote the same helper independently, twice with
byte-identical statements. If you need a fact about `CtxOk2`, `Sat2`
or hoisted `AnnotOk2`, **it is probably already below.**

*Context predicate.* `CtxOk2`; `CtxOk2Ann` (the proposed fourth leaf
conjunct, stated beside — see generation five).

*Context — reading and restriction.* `fvar_leaf`, `fvar_ty`, `length`,
`nil`, `of_fvarLeaves_nil`, `of_cover`, `of_subset`, `wScoped`
(`CtxOk2` carries its own scoping — do not add a `WScoped` premise).

*Context — structural projections.* `app`, `app_fn`, `app_arg`,
`forallE_ty`, `forallE_body`, `lam_ty`, `lam_body`, `letE_ty`,
`letE_val`, `letE_body`, `proj_arg`.

*Context — fuel and depth.* `fuelMono`, `mono`, `weakenTop`,
`denote2_shiftFrom`, `denote2_weaken_top`.

*Context — binder opening.* `open`, `openS`, **`openCongC`** (the
generation-four shape: takes `DefEqClaims2C`'s conclusion directly),
`openCong` (generation-three shape, kept because prose cites it).

*`AnnotOk2` splitters, hoisted.* `hoist_pi`, `hoist_lam`, `hoist_app`,
`hoist_letE`, `hoist_proj`, `hoist_eqE`, `hoist_beta_pos`,
`hoist_zeta`.

*`AnnotOk2` converses* (generation four made the claims *deliver* a
ρ-uniform `AnnotOk2`, so these are newly owed): `of_pi`, `of_lam`,
`of_app`, `of_letE`, `of_letE_raw`, `of_proj`, `of_eqE`.

*Context transfer across a domain equality.* `Sat2.head_congr`,
`AnnotOk2.hoist_head_congr`, `AnnotOk2.hoist_lift`.

*Leaf grading.* `annotOk2_of_denote2_const`.

*Generation five.* The whole of the above is lifted to `CtxOk2D`
(`Interp2/CtxOk2D.lean`) — same names, same order, `CtxOk2D.` in place
of `CtxOk2.`.  **Check there first if you are working against
`Claims2D`.** Three entries take one extra argument in the lifted
form, the domain's hoisted grading: `open`, `openS`, `openCongC`.

**Two shapes are deliberately absent because they are false**, and are
documented at their sites: there is **no `letE` binder splitter**
(`AnnotOk2`'s `letE` clause reads the body at the *value's* point,
while `Sat2 (T :: Δa)` only constrains the head to *inhabit* `T`;
`hoist_zeta` is the usable form and the one the checker needs), and
**no unconditional `of_lam`** (the λ's fibre component is a genuinely
per-valuation fact with no hereditary source). If you find yourself
wanting either, you have the wrong shape, not a missing lemma.
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
theorem infer_sort_claim2 (m : EnvS2UM V μ env) {d : Nat} {u : Level}
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
theorem infer_fvar_claim2 (m : EnvS2UM V μ env) {d idx : Nat} {n : Name}
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
theorem infer_bvar_claim2 (m : EnvS2UM V μ env) {d i : Nat} {t : Expr}
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
def CtxOk2 {env : Env} (m : EnvS2UM V μ env) (μ : CheckMode)
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
theorem CtxOk2.fvar_leaf {env : Env} {m : EnvS2UM V μ env}
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

variable {m : EnvS2UM V μ env}

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
to add; until then every consumer of `CtxOk2.open` passes it along.

**Landed (seal 8): `EnvS2.acval_closed` is that field.**  The kit below
therefore takes neither `henv` nor `hacl` — it reads `m.base.wf` and
`m.acval_closed` out of the structure.  `CtxOk2.open` above keeps its
explicit premises because its signature is already cited. -/

/-! ## The seal-11 kit — what the family-wide move to `CtxOk2` needs

`CtxOk2R` is false premise-free (`Step2/CtxOk2RRefute.lean`), so all
four claims take `CtxOk2` and the 54 `CtxOkR` uses in `Step2/Whnf.lean`
and `Step2/DefEqRun.lean` must re-point.  41 are pure `fvarLeaves`
re-plumbing the kit above already covers.  The rest are here. -/

/-- A closed expression's context correspondence is free.  Transpose of
`CtxOkR.of_fvarLeaves_nil` (`Bridge/Stuck.lean`), which is used at
eight sites in `DefEqRun.lean`.  Contentless: with no leaves there is
no package to build. -/
theorem CtxOk2.of_fvarLeaves_nil {F d : Nat} {Δa : List AVExpr}
    {e : Expr} (hlen : Δa.length = d) (h : e.fvarLeaves = []) :
    CtxOk2 m μ φ F d Δa e :=
  ⟨hlen, fun l hl => by rw [h] at hl; exact absurd hl (by simp)⟩

/-! ### `CtxOk2` already carries its own scoping

The two lemmas below are why the kit needs no `WScoped` premises: the
leaf package's *syntactic* half — `l.1 < d` and
`Expr.fvarsBelow l.1 l.2.2` at every leaf, **hereditarily**, since
`Expr.fvarLeaves` descends into annotations — is exactly `WScoped`
unrolled.  Established here so that `CtxOk2.openCong` and
`CtxOk2.openS` can take a `CtxOk2` where `CtxOkR.open`'s transpose
takes a scoping hypothesis. -/

/-- Leafwise index bounds give the direct bound. -/
private theorem fvarsBelow_of_leaves : ∀ (e : Expr) {d : Nat},
    (∀ l ∈ e.fvarLeaves, l.1 < d) → Expr.fvarsBelow d e := by
  intro e
  induction e with
  | fvar idx n ty ih =>
    intro d h
    exact h (idx, n, ty) (by simp [Setlec.Expr.fvarLeaves])
  | app f a ihf iha =>
    intro d h
    exact ⟨ihf (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl])),
      iha (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl]))⟩
  | lam _ ty b _ iht ihb =>
    intro d h
    exact ⟨iht (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl])),
      ihb (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl]))⟩
  | forallE _ ty b _ iht ihb =>
    intro d h
    exact ⟨iht (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl])),
      ihb (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl]))⟩
  | letE _ t v b iht ihv ihb =>
    intro d h
    exact ⟨iht (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl])),
      ihv (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl])),
      ihb (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl]))⟩
  | proj _ _ e ih =>
    intro d h
    exact ih (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl]))
  | _ => intro d _; trivial

/-- Leafwise annotation bounds upgrade a direct bound to `WScoped`.
The `fvar` case is the whole content: the *leaf's own*
`fvarsBelow idx ty` is what lets the recursion drop from `d` to `idx`,
which a plain `fvarsBelow d` hypothesis could not do. -/
private theorem wScoped_of_leaves : ∀ (e : Expr) {d : Nat},
    Expr.fvarsBelow d e →
    (∀ l ∈ e.fvarLeaves, Expr.fvarsBelow l.1 l.2.2) →
    Expr.WScoped d e := by
  intro e
  induction e with
  | fvar idx n ty ih =>
    intro d hfb h
    rw [Setlec.Expr.WScoped]
    refine ⟨hfb, ih (h (idx, n, ty) (by simp [Setlec.Expr.fvarLeaves]))
      (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl]))⟩
  | app f a ihf iha =>
    intro d hfb h
    rw [Setlec.Expr.WScoped]
    exact ⟨ihf hfb.1
        (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl])),
      iha hfb.2
        (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl]))⟩
  | lam _ ty b _ iht ihb =>
    intro d hfb h
    rw [Setlec.Expr.WScoped]
    exact ⟨iht hfb.1
        (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl])),
      ihb hfb.2
        (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl]))⟩
  | forallE _ ty b _ iht ihb =>
    intro d hfb h
    rw [Setlec.Expr.WScoped]
    exact ⟨iht hfb.1
        (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl])),
      ihb hfb.2
        (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl]))⟩
  | letE _ t v b iht ihv ihb =>
    intro d hfb h
    rw [Setlec.Expr.WScoped]
    exact ⟨iht hfb.1
        (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl])),
      ihv hfb.2.1
        (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl])),
      ihb hfb.2.2
        (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl]))⟩
  | proj _ _ e ih =>
    intro d hfb h
    rw [Setlec.Expr.WScoped]
    exact ih hfb
      (fun l hl => h l (by simp [Setlec.Expr.fvarLeaves, hl]))
  | _ => intro d _ _; rw [Setlec.Expr.WScoped]; trivial

/-- **`CtxOk2` implies well-scopedness.**  Not a convenience: it is
what makes the two opening lemmas below take no scoping premise, and
what makes `CtxOk2Open` (`Step2/InferQ.lean`) satisfiable *as stated*,
with neither `WScoped` hypothesis it omits. -/
theorem CtxOk2.wScoped {F d : Nat} {Δa : List AVExpr} {e : Expr}
    (hC : CtxOk2 m μ φ F d Δa e) : Expr.WScoped d e :=
  wScoped_of_leaves e
    (fvarsBelow_of_leaves e (fun l hl => (hC.2 l hl).1))
    (fun l hl => (hC.2 l hl).2.1)

/-- **`CtxOk2Open`'s body, verbatim** (`Step2/InferQ.lean`), as a
theorem.  The residue's own premises suffice: `EnvWF` is `m.base.wf`,
`hacl` is `m.acval_closed`, and the two `WScoped` hypotheses
`CtxOk2.open` asks for are `CtxOk2.wScoped` of the two contexts it is
already handed.  The `fvarsBelow` argument is then redundant; it is
kept so the signature matches the residue. -/
theorem CtxOk2.openS {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty body : Expr} {ta : AVExpr}
    (ht : CtxOk2 m μ φ F d Δa ty) (hb : CtxOk2 m μ φ F d Δa body)
    (hty : denote2 μ m.acval env φ F d ty = some ta)
    (_hfb : Expr.fvarsBelow d ty) :
    CtxOk2 m μ φ F (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d n ty)) :=
  CtxOk2.open m.base.wf m.acval_closed hb ht hb.wScoped ht.wScoped hty

/-- **Opening a binder congruence, annotated.**  The transpose of
`CtxOkR.openCong` (`Bridge/DefEq.lean`), and the one genuine *read* of
the context hypothesis among the 54 `CtxOkR` uses the seal-11 move has
to re-point.

At a `∀`/`λ` congruence `defeqStep` opens each side's body with **its
own** annotation, so the right body sits in a context whose head is the
**left** domain `ta₁` while the opened variable's annotation denotes
the **right** one `ta₂`.  `CtxOkR` absorbs that with a bare
`DefEq A₁ A₂`; here the currency is `interp2` and the premise is the
domains' semantic agreement — and `hdom` is **literally
`DefEqClaims2C`'s conclusion, partially applied**: the same `∀ ρ`, the
same `Sat2 V Δa ρ`, the same `interp2` equality, with nothing between
them.  Under `Claims2B` that conclusion still carried the two ρ-local
`AnnotOk2` arguments, which is why `CtxOk2.openCong` below (the
generation-three signature, kept) has them; generation four hoists them
into the claim's premises and this lemma no longer asks.

The grading `hok₁`/`hok₂` is therefore *not* a premise here at all.  It
is still needed at the call site — to invoke `DefEqClaims2C` in the
first place — but it is exactly that claim's own two hoisted premises,
so the site pays for it once rather than twice. -/
theorem CtxOk2.openCongC {F d : Nat} {Δa : List AVExpr}
    {body ty : Expr} {n : Name} {ta₁ ta₂ : AVExpr}
    (hb : CtxOk2 m μ φ F d Δa body) (ht : CtxOk2 m μ φ F d Δa ty)
    (hty : denote2 μ m.acval env φ F d ty = some ta₂)
    (hdom : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ ta₁ = interp2 V ρ ta₂) :
    CtxOk2 m μ φ F (d + 1) (ta₁ :: Δa)
      (body.instantiate1 (.fvar d n ty)) := by
  have henv := m.base.wf
  have hacl := m.acval_closed
  have hwb : Expr.WScoped d body := hb.wScoped
  have hwt : Expr.WScoped d ty := ht.wScoped
  refine ⟨by simp [hb.1], fun l hl => ?_⟩
  rcases Setlec.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
  · exact (CtxOk2.weakenTop (Ba := ta₁) henv hacl hwb hb).2 l hl'
  · rw [Setlec.Expr.fvarLeaves] at hl'
    rcases List.mem_cons.mp hl' with rfl | hl''
    · refine ⟨by omega, hwt.fvarsBelow, ta₂.liftN 1 0, ta₁, ?_, ?_, ?_⟩
      · rw [denote2_weaken_top henv hacl hwt, hty]
        rfl
      · rw [show d + 1 - 1 - d = 0 from by omega]
        rfl
      · intro ρ hρ
        have hρ' : Sat2 V Δa (fun j => ρ (j + 1)) := Sat2_tail hρ
        show interp2 V ρ (AVExpr.liftN 1 ta₂ 0)
          = interp2 V (fun j => ρ (j + (d + 1 - 1 - d) + 1)) ta₁
        rw [show d + 1 - 1 - d = 0 from by omega,
          show AVExpr.liftN 1 ta₂ 0 = ta₂.lift from rfl,
          interp2_lift (V := V) ta₂ ρ]
        exact (hdom _ hρ').symm
    · exact (CtxOk2.weakenTop (Ba := ta₁) henv hacl hwt ht).2 l hl''

/-- The generation-three signature, kept because it is cited in this
file's prose and in DESIGN's seal 13.  Its `hdom` still carries the two
ρ-**local** `AnnotOk2` arguments that `DefEqClaims2B`'s conclusion had;
under `Claims2C` those have moved above the `∀ ρ`, so `openCongC` is
the shape a consumer now holds and this one is its specialization. -/
theorem CtxOk2.openCong {F d : Nat} {Δa : List AVExpr}
    {body ty : Expr} {n : Name} {ta₁ ta₂ : AVExpr}
    (hb : CtxOk2 m μ φ F d Δa body) (ht : CtxOk2 m μ φ F d Δa ty)
    (hty : denote2 μ m.acval env φ F d ty = some ta₂)
    (hok₁ : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta₁)
    (hok₂ : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta₂)
    (hdom : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta₁ →
      AnnotOk2 V ρ ta₂ → interp2 V ρ ta₁ = interp2 V ρ ta₂) :
    CtxOk2 m μ φ F (d + 1) (ta₁ :: Δa)
      (body.instantiate1 (.fvar d n ty)) :=
  CtxOk2.openCongC hb ht hty
    fun ρ hρ => hdom ρ hρ (hok₁ ρ hρ) (hok₂ ρ hρ)

/-! ### Consumer note: the grading is `∀ ρ`; `DefEqClaims2B`'s is not

`hdom` is free at the five congruence sites — it is exactly
`ihd hdt … hta₁ hta₂`, `DefEqClaims2B`'s conclusion before its `ρ`.
`hok₁`/`hok₂` are **not**: `DefEqClaims2B` takes its two `AnnotOk2`
*under* `∀ ρ`, so a site that has run `intro ρ hρ hokA hokB` holds them
at one valuation only, while `CtxOk2` — being a `∀ ρ` statement about
the *extended* context — asks for them at every valuation satisfying
`Δa`.

That gap is not closable inside this lemma, and it is not an artifact
of how `openCong` is stated: the new leaf's link is
`interp2 ρ' (ta₂.lift) = interp2 (ρ' ∘ (· + 1)) ta₁` for every `ρ'`
with `Sat2 (ta₁ :: Δa) ρ'`, and `Sat2` supplies only inhabitation of
the head, never truthfulness of it.  Reported at the junction; the
cheap repair is to **hoist** `DefEqClaims2B`'s two `AnnotOk2` above its
`∀ ρ`, which is self-propagating at the congruence (the node's hoisted
`AnnotOk2_pi`/`AnnotOk2_lam` split gives the domain's hoisted form
directly, and the codomain's at `cons x ρ` is `Sat2`'s own cons). -/

/-! ### Both halves of the grading question, mechanized

The negative half first: the ρ-local grading is not merely too weak
for the proof above, it makes the lemma **false**.  Then the positive
half: the hoist is self-propagating, so the repair the negative half
forces costs the congruences nothing. -/

/-- **`CtxOk2.openCong` with the grading localized to one valuation** —
`DefEqClaims2B`'s `AnnotOk2`/equality package exactly as a site holds
it after `intro ρ hρ hokA hokB`.  Both domains are fully certified
(`ty₁` carries its own `denote2` *and* `CtxOk2`), so this is as strong
a shape as a congruence site could ask for. -/
def OpenCongLocal {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) : Prop :=
  ∀ {F d : Nat} {Δa : List AVExpr} {body ty ty₁ : Expr} {n : Name}
    {ta₁ ta₂ : AVExpr},
    CtxOk2 m μ φ F d Δa body → CtxOk2 m μ φ F d Δa ty →
    CtxOk2 m μ φ F d Δa ty₁ →
    denote2 μ m.acval env φ F d ty = some ta₂ →
    denote2 μ m.acval env φ F d ty₁ = some ta₁ →
    (∃ ρ : Nat → V, Sat2 V Δa ρ ∧ AnnotOk2 V ρ ta₁ ∧
      AnnotOk2 V ρ ta₂ ∧ interp2 V ρ ta₁ = interp2 V ρ ta₂) →
    CtxOk2 m μ φ F (d + 1) (ta₁ :: Δa)
      (body.instantiate1 (.fvar d n ty))

/-- **The ρ-local grading is refuted, premise-free.**  No environment
shape, no fuel, no mode, no level assignment.

The witness is one binder deep and needs no `#100` subtlety: at
`d = 1`, `Δa = [⟪Sort 1⟫]`, the right domain is the context variable
(`ta₂ = .bvar 0`, ρ-dependent) and the left is `⟪Sort 0⟫` (closed).
They agree at `ρ ≡ univ 0`, which is the one valuation the site holds.
The extended context's leaf link, however, is quantified over *every*
`ρ` satisfying `[⟪Sort 0⟫, ⟪Sort 1⟫]`, and at `ρ ≡ ∅` — legitimate,
since `∅ ∈ˢ univ n` — it demands `∅ = univ 0`, whence `∅ ∈ˢ ∅`.

*This is why `CtxOk2.openCong`'s `hok₁`/`hok₂` are `∀ ρ`, and why the
family-wide move needs `DefEqClaims2B`'s two `AnnotOk2` hoisted above
its `∀ ρ`.  The grading is not the problem; the quantifier is.* -/
theorem not_openCongLocal {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) : ¬ OpenCongLocal m φ := by
  intro h
  have hlen : ([AVExpr.sort 1] : List AVExpr).length = 1 := rfl
  have hb : CtxOk2 m μ φ 1 1 [AVExpr.sort 1] (.bvar 0) :=
    CtxOk2.of_fvarLeaves_nil hlen (by simp [Setlec.Expr.fvarLeaves])
  have ht₁ : CtxOk2 m μ φ 1 1 [AVExpr.sort 1] (.sort .zero) :=
    CtxOk2.of_fvarLeaves_nil hlen (by simp [Setlec.Expr.fvarLeaves])
  have ht : CtxOk2 m μ φ 1 1 [AVExpr.sort 1]
      (.fvar 0 .anonymous (.sort (.succ .zero))) := by
    refine ⟨hlen, fun l hl => ?_⟩
    simp only [Setlec.Expr.fvarLeaves, List.mem_singleton] at hl
    subst hl
    exact ⟨by omega, trivial, .sort 1, .sort 1,
      by rw [denote2]; rfl, rfl, fun _ _ => rfl⟩
  have hty : denote2 μ m.acval env φ 1 1
      (.fvar 0 .anonymous (.sort (.succ .zero)))
      = some (AVExpr.bvar 0) := by rw [denote2]
  have hty₁ : denote2 μ m.acval env φ 1 1 (.sort .zero)
      = some (AVExpr.sort 0) := by rw [denote2]; rfl
  have hex : ∃ ρ : Nat → V, Sat2 V [AVExpr.sort 1] ρ ∧
      AnnotOk2 V ρ (.sort 0) ∧ AnnotOk2 V ρ (.bvar 0) ∧
      interp2 V ρ (.sort 0) = interp2 V ρ (.bvar 0) := by
    refine ⟨fun _ => univ 0, ?_, by simp, by simp, by simp⟩
    intro i Aa hi
    cases i with
    | zero =>
      obtain rfl : AVExpr.sort 1 = Aa := by simpa using hi
      simpa using univ_mem_univ (V := V) 0
    | succ i => simp at hi
  obtain ⟨-, hleaf⟩ :=
    h (n := .anonymous) hb ht ht₁ hty hty₁ hex
  obtain ⟨-, -, tya, Aa, h1, h2, h3⟩ :=
    hleaf (1, .anonymous, .fvar 0 .anonymous (.sort (.succ .zero)))
      (by simp [Setlec.Expr.fvarLeaves])
  rw [denote2] at h1
  obtain rfl : AVExpr.bvar 1 = tya := Option.some.inj h1
  obtain rfl : AVExpr.sort 0 = Aa := Option.some.inj h2
  have hsat : Sat2 V [AVExpr.sort 0, AVExpr.sort 1]
      (fun _ => empty) := by
    intro i Aa hi
    cases i with
    | zero =>
      obtain rfl : AVExpr.sort 0 = Aa := by simpa using hi
      simpa using empty_mem_univ (V := V) 0
    | succ i =>
      cases i with
      | zero =>
        obtain rfl : AVExpr.sort 1 = Aa := by simpa using hi
        simpa using empty_mem_univ (V := V) 1
      | succ i => simp at hi
  have hbad : (empty : V) = univ 0 := by
    have := h3 (fun _ => empty) hsat
    simpa using this
  exact not_mem_empty (V := V) empty (hbad ▸ empty_mem_univ (V := V) 0)

/-- **The positive half: the hoist is self-propagating at a `∀`.**  A
hoisted `AnnotOk2` of the node gives the domain's hoisted form and the
codomain's *in the extended context*, which is exactly the pair the
recursive call needs.  So paying the repair at the congruence costs
nothing beyond restating it. -/
theorem AnnotOk2.hoist_pi {Δa : List AVExpr} {u v : Nat} {A B : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.pi u v A B)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ A) ∧
      (∀ ρ : Nat → V, Sat2 V (A :: Δa) ρ → AnnotOk2 V ρ B) := by
  refine ⟨fun ρ hρ => ((AnnotOk2_pi V ρ u v A B) ▸ h ρ hρ).1,
    fun ρ hρ => ?_⟩
  have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
    funext i; cases i with | zero => rfl | succ i => rfl
  have := ((AnnotOk2_pi V _ u v A B) ▸ h _ (Sat2_tail hρ)).2
    (ρ 0) (hρ 0 A rfl)
  rwa [hcons] at this

/-- **`CtxOk2.openCong`'s premises are jointly satisfiable** — the
lemma is not a vacuous one whose `∀ ρ` grading no instance can meet.
The diagonal at a sort: both domains are `⟪Sort 0⟫`, whose `AnnotOk2`
is free at every valuation. -/
example (m : EnvS2UM V μ env) (φ : Name → Nat)
    (nm : Name) :
    CtxOk2 m μ φ 1 1 [AVExpr.sort 0]
      ((Expr.bvar 0).instantiate1 (.fvar 0 nm (.sort .zero))) :=
  CtxOk2.openCong (ta₁ := .sort 0)
    (CtxOk2.of_fvarLeaves_nil rfl (by simp [Setlec.Expr.fvarLeaves]))
    (CtxOk2.of_fvarLeaves_nil rfl (by simp [Setlec.Expr.fvarLeaves]))
    (by rw [denote2]; rfl) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ _ _ _ => rfl)

/-- The same at a `λ`, where the node's second component has the same
shape.  Together these cover all five congruence sites. -/
theorem AnnotOk2.hoist_lam {Δa : List AVExpr} {v : Nat} {A b : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.lam v A b)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ A) ∧
      (∀ ρ : Nat → V, Sat2 V (A :: Δa) ρ → AnnotOk2 V ρ b) := by
  refine ⟨fun ρ hρ => ((AnnotOk2_lam V ρ v A b) ▸ h ρ hρ).1,
    fun ρ hρ => ?_⟩
  have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
    funext i; cases i with | zero => rfl | succ i => rfl
  have := ((AnnotOk2_lam V _ v A b) ▸ h _ (Sat2_tail hρ)).2.1
    (ρ 0) (hρ 0 A rfl)
  rwa [hcons] at this

/-! ## The hoist kit, generation four — the complete list

`hoist_pi`/`hoist_lam` above are the two shapes the congruences named,
and they are stated exactly as a consumer holding
`∀ ρ, Sat2 V Δa ρ → AnnotOk2 V ρ (.pi u v A B)` wants them: the
domain's hoisted form over `Δa`, and the codomain's hoisted form over
the **extended** context `A :: Δa`.  That is the pair a recursive call
into the claim family takes.

Audited against that use, three things were missing and are added
here.

1. **The non-binder splitters** (`hoist_app`, `hoist_letE`,
   `hoist_proj`, `hoist_eqE`) and the two contraction forms
   (`hoist_beta_pos`, `hoist_zeta`).  Mechanical, but a quarter that
   re-derives them re-derives them four times.
2. **The converses** (`of_pi`, `of_lam`, `of_app`, `of_letE`,
   `of_proj`, `of_eqE`).  `WhnfCoreClaims2C`/`WhnfClaims2C` and
   `InferClaims2C` now *deliver* a ρ-uniform `AnnotOk2`, so assembling
   the node fact from its parts' hoisted forms is an obligation this
   generation created.  `Sat2_cons` is the whole content of the binder
   ones; the semantic components (the `λ`'s fibre, the app's slot)
   stay per-valuation, because they are memberships and not gradings.
3. **The head transfer** (`Sat2.head_congr`,
   `AnnotOk2.hoist_head_congr`) — *the piece without which the split
   kit does not reach its own motivating site.*  `CtxOk2.openCong`
   extends the context with the **left** domain `ta₁`, while
   `hoist_pi`/`hoist_lam` deliver the right side's codomain fact over
   `ta₂ :: Δa`.  The two lists differ in their head and nothing else
   relates them; the bridge is the domains' own semantic agreement,
   which is `DefEqClaims2C`'s conclusion — already in hand at every
   congruence.

**Two shapes are deliberately absent, and the absence is a finding.**

* There is **no `letE` binder splitter**.  `AnnotOk2`'s `letE` clause
  reads the body at `cons (interp2 V ρ v) ρ` — the *value's* point —
  while `Sat2 (T :: Δa) ρ'` constrains `ρ' 0` only to inhabit `T`.  So
  the body's fact does not hoist into the extended context, and no
  restatement of the hoist repairs that.  `hoist_zeta` is what a
  consumer gets instead, and it is what the checker needs: `letE` is
  reduced by substitution, not by opening.
* There is **no unconditional `of_lam`**.  The `λ` clause's fibre
  component is a genuinely per-valuation semantic fact with no
  hereditary source, so the converse takes it as a premise. -/

/-- The application splits into its two parts, both hoisted.  The slot
component stays per-valuation: it is a membership, not a grading. -/
theorem AnnotOk2.hoist_app {Δa : List AVExpr} {f a : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.app f a)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ f) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ a) :=
  ⟨fun ρ hρ => ((AnnotOk2_app V ρ f a) ▸ h ρ hρ).1,
    fun ρ hρ => ((AnnotOk2_app V ρ f a) ▸ h ρ hρ).2.1⟩

/-- The `letE`'s two *unopened* parts.  The body is not here — see the
kit's note; `hoist_zeta` is its usable form. -/
theorem AnnotOk2.hoist_letE {Δa : List AVExpr} {T v b : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.letE T v b)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ T) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ v) :=
  ⟨fun ρ hρ => ((AnnotOk2_letE V ρ T v b) ▸ h ρ hρ).1,
    fun ρ hρ => ((AnnotOk2_letE V ρ T v b) ▸ h ρ hρ).2.1⟩

/-- The projection's subject. -/
theorem AnnotOk2.hoist_proj {Δa : List AVExpr} {i : Nat} {e : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.proj i e)) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ e :=
  fun ρ hρ => ((AnnotOk2_proj V ρ i e) ▸ h ρ hρ).1

/-- The equality node's two sides. -/
theorem AnnotOk2.hoist_eqE {Δa : List AVExpr} {T a b : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.eqE T a b)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ a) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ b) :=
  ⟨fun ρ hρ => ((AnnotOk2_eqE V ρ T a b) ▸ h ρ hρ).1,
    fun ρ hρ => ((AnnotOk2_eqE V ρ T a b) ▸ h ρ hρ).2⟩

/-- The β contractum, hoisted, at a positive codomain kind. -/
theorem AnnotOk2.hoist_beta_pos {Δa : List AVExpr} {v : Nat}
    (hv : v ≠ 0) {A b a : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOk2 V ρ (.app (.lam v A b) a)) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (b.inst a) :=
  fun ρ hρ => (AnnotOk2_beta_pos V hv (h ρ hρ)).2

/-- The ζ contractum, hoisted — the `letE` body's usable form. -/
theorem AnnotOk2.hoist_zeta {Δa : List AVExpr} {T v b : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.letE T v b)) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (b.inst v) :=
  fun ρ hρ => (AnnotOk2_zeta V (h ρ hρ)).2

/-! ### The converses -/

/-- **The converse at a `Π`.**  `Sat2_cons` is the whole content: an
inhabitant of the domain extends the valuation into `A :: Δa`. -/
theorem AnnotOk2.of_pi {Δa : List AVExpr} {u v : Nat} {A B : AVExpr}
    (hA : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ A)
    (hB : ∀ ρ : Nat → V, Sat2 V (A :: Δa) ρ → AnnotOk2 V ρ B) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.pi u v A B) := by
  intro ρ hρ
  rw [AnnotOk2_pi]
  exact ⟨hA ρ hρ, fun x hx => hB _ (Sat2_cons (V := V) hρ hx)⟩

/-- **The converse at a `λ`.**  The fibre component has no hereditary
source and is therefore a premise, stated per-valuation because that
is what it is. -/
theorem AnnotOk2.of_lam {Δa : List AVExpr} {v : Nat} {A b : AVExpr}
    (hA : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ A)
    (hb : ∀ ρ : Nat → V, Sat2 V (A :: Δa) ρ → AnnotOk2 V ρ b)
    (hfib : ∀ ρ : Nat → V, Sat2 V Δa ρ → ∃ B : V → V,
      (∀ x, x ∈ˢ interp2 V ρ A → interp2 V (cons x ρ) b ∈ˢ B x) ∧
      (v = 0 → ∀ x, x ∈ˢ interp2 V ρ A →
        B x ∈ˢ (univZero : V))) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.lam v A b) := by
  intro ρ hρ
  rw [AnnotOk2_lam]
  exact ⟨hA ρ hρ, fun x hx => hb _ (Sat2_cons (V := V) hρ hx),
    hfib ρ hρ⟩

/-- **The converse at an application.**  The slot stays
per-valuation; `AnnotOk2_app_of` (`Annot/Ok2.lean`) is the shape that
builds it from an annotated `Π`. -/
theorem AnnotOk2.of_app {Δa : List AVExpr} {f a : AVExpr}
    (hf : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ f)
    (ha : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ a)
    (hslot : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      ∃ (v : Nat) (A : V) (B : V → V),
        interp2 V ρ f ∈ˢ piR v A B ∧ interp2 V ρ a ∈ˢ A ∧
        (v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V))) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.app f a) := by
  intro ρ hρ
  rw [AnnotOk2_app]
  exact ⟨hf ρ hρ, ha ρ hρ, hslot ρ hρ⟩

/-- **The converse at a `letE`**, in the form the extended context can
actually supply: the value inhabits the annotation, so `Sat2_cons`
puts the body's hoisted fact at exactly the point the clause reads. -/
theorem AnnotOk2.of_letE {Δa : List AVExpr} {T v b : AVExpr}
    (hT : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ T)
    (hv : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ v)
    (hmem : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ v ∈ˢ interp2 V ρ T)
    (hb : ∀ ρ : Nat → V, Sat2 V (T :: Δa) ρ → AnnotOk2 V ρ b) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.letE T v b) := by
  intro ρ hρ
  rw [AnnotOk2_letE]
  exact ⟨hT ρ hρ, hv ρ hρ,
    hb _ (Sat2_cons (V := V) hρ (hmem ρ hρ))⟩

/-- The converse at a `letE` with the body's fact in its raw,
value-indexed form — for a consumer that has no membership to spend. -/
theorem AnnotOk2.of_letE_raw {Δa : List AVExpr} {T v b : AVExpr}
    (hT : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ T)
    (hv : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ v)
    (hb : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOk2 V (cons (interp2 V ρ v) ρ) b) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.letE T v b) := by
  intro ρ hρ
  rw [AnnotOk2_letE]
  exact ⟨hT ρ hρ, hv ρ hρ, hb ρ hρ⟩

/-- The converse at a projection. -/
theorem AnnotOk2.of_proj {Δa : List AVExpr} {i : Nat} {e : AVExpr}
    (he : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ e) (hi : i < 2)
    (hsig : ∀ ρ : Nat → V, Sat2 V Δa ρ → ∃ u v A Bf,
      interp2 V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
      A ∈ˢ (univ u : V) ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ (univ v : V)) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.proj i e) := by
  intro ρ hρ
  rw [AnnotOk2_proj]
  exact ⟨he ρ hρ, hi, hsig ρ hρ⟩

/-- The converse at an equality node. -/
theorem AnnotOk2.of_eqE {Δa : List AVExpr} {T a b : AVExpr}
    (ha : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ a)
    (hb : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ b) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ (.eqE T a b) := by
  intro ρ hρ
  rw [AnnotOk2_eqE]
  exact ⟨ha ρ hρ, hb ρ hρ⟩

/-! ### The head transfer — what makes the kit reach `openCong`

Without these two the split kit stops one step short of the sites it
was built for: `hoist_pi`/`hoist_lam` hand the right side's codomain
fact over `ta₂ :: Δa`, and the recursive call runs in `ta₁ :: Δa`. -/

/-- **A satisfying valuation transfers across a head equality.**
`Sat2` reads the head at the *tail* valuation, which is exactly where
the domains' agreement is stated, so the transfer is immediate. -/
theorem Sat2.head_congr {Δa : List AVExpr} {A B : AVExpr}
    {ρ : Nat → V}
    (heq : ∀ ρ' : Nat → V, Sat2 V Δa ρ' →
      interp2 V ρ' A = interp2 V ρ' B)
    (hρ : Sat2 V (A :: Δa) ρ) : Sat2 V (B :: Δa) ρ := by
  intro i Aa hi
  cases i with
  | zero =>
    obtain rfl : B = Aa := by simpa using hi
    have h0 : ρ 0 ∈ˢ interp2 V (fun j => ρ (j + 1)) A := hρ 0 A rfl
    show ρ 0 ∈ˢ interp2 V (fun j => ρ (j + 1)) B
    rwa [heq _ (Sat2_tail hρ)] at h0
  | succ i => exact hρ (i + 1) Aa (by simpa using hi)

/-- **A hoisted fact transfers with it.**  `heq` is
`DefEqClaims2C`'s conclusion; `h` is `hoist_pi.2`/`hoist_lam.2` on the
right side; the result is what the recursive call in `ta₁ :: Δa`
takes. -/
theorem AnnotOk2.hoist_head_congr {Δa : List AVExpr} {A B e : AVExpr}
    (heq : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ A = interp2 V ρ B)
    (h : ∀ ρ : Nat → V, Sat2 V (B :: Δa) ρ → AnnotOk2 V ρ e) :
    ∀ ρ : Nat → V, Sat2 V (A :: Δa) ρ → AnnotOk2 V ρ e :=
  fun ρ hρ => h ρ (Sat2.head_congr heq hρ)

/-- **Weakening a hoisted fact under one more binder.**  The
annotation lifts and `Sat2_tail` carries the valuation; the transpose
of `CtxOk2.weakenTop` for the grading. -/
theorem AnnotOk2.hoist_lift {Δa : List AVExpr} {X e : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ e) :
    ∀ ρ : Nat → V, Sat2 V (X :: Δa) ρ → AnnotOk2 V ρ e.lift := by
  intro ρ hρ
  refine (AnnotOk2_liftN V 1 e 0 ρ).mpr ?_
  rw [shiftE_zero]
  exact h _ (Sat2_tail hρ)

/-! ### Trap-check on the kit

Every lemma above is an implication between `∀ ρ, Sat2 → …` shapes and
mentions no fuel, no `denote2` and no run, so the smallest-fuel test
has nothing to bite on — and, per seal 11, that is *not* a clean bill
of health on its own.  The semantic check that matters is inhabitation
in a *non-vacuous* context, which the two examples below give: the
splitters and the converses are exercised at a `Δa` whose `Sat2` is
satisfiable, so neither direction is a vacuous implication. -/

/-- `ρ ≡ ∅` satisfies `[⟪Sort 0⟫]`: the context used below is
genuinely inhabited. -/
private theorem sat2_sort0_empty :
    Sat2 V [AVExpr.sort 0] (fun _ => (empty : V)) := by
  intro i Aa hi
  cases i with
  | zero =>
    obtain rfl : AVExpr.sort 0 = Aa := by simpa using hi
    simpa using empty_mem_univ (V := V) 0
  | succ i => simp at hi

/-- The converse builds a `Π` fact over that context and the splitter
takes it back apart, so neither direction of the kit is a vacuous
implication. -/
example :
    AnnotOk2 V (fun _ => (empty : V))
      (.pi 1 2 (.sort 0) (.sort 1)) ∧
    (∀ ρ : Nat → V, Sat2 V [AVExpr.sort 0] ρ →
      AnnotOk2 V ρ (AVExpr.sort 0)) := by
  have hpi : ∀ ρ : Nat → V, Sat2 V [AVExpr.sort 0] ρ →
      AnnotOk2 V ρ (.pi 1 2 (.sort 0) (.sort 1)) :=
    AnnotOk2.of_pi (fun _ _ => by simp) (fun _ _ => by simp)
  exact ⟨hpi _ sat2_sort0_empty, (AnnotOk2.hoist_pi hpi).1⟩

/-! ## The clauses, re-pointed to `Claims2C`

`InferClaims2C` splits the old single `∀ ρ, Sat2 → AnnotOk2 ea ∧ …`
into **three** ρ-uniform conjuncts: the subject's grading, the
*returned type's* grading (new this generation — it is what retires
`TypeOk2`), and the membership.  The first and third are the sealed
conclusion re-associated; the second is the new obligation, and it is
the one worth auditing clause by clause.

* **`.sort`** — free.  The returned type is `.sort (u.eval φ + 1)` and
  the `sort` clause of `AnnotOk2` is `True`.
* **`.bvar`** — free, and vacuously: the checker throws.
* **`.fvar`** — **not free.**  See the STOP note below. -/

/-- **A `.const`'s annotation is an `acval` leaf**, hence truthful at
every valuation.  `denote2`'s `const` clause emits
`acval n (substFn …)` or nothing, and `EnvS2.acval_ok2` grades every
such leaf unconditionally — no `Sat2` spent, no fuel condition.

Stated here rather than at a clause because *every* quarter's clauses
whose returned type is a stored constant (`.const`, the two literal
clauses, the recursor and projection exits) need exactly this for
`InferClaims2C`'s new conjunct. -/
theorem annotOk2_of_denote2_const {F d : Nat} {n : Name}
    {us : List Level} {ta : AVExpr}
    (h : denote2 μ m.acval env φ F d (.const n us) = some ta)
    (ρ : Nat → V) : AnnotOk2 V ρ ta := by
  rw [denote2] at h
  cases hf : env.find? n with
  | none => rw [hf] at h; exact nomatch h
  | some ci =>
    rw [hf] at h
    dsimp only at h
    split at h
    · obtain rfl := Option.some.inj h
      exact m.acval_ok2 _ _ ρ
    · exact nomatch h

/-! ### STOP — `CtxOk2` does not carry the leaf annotation's grading

`InferClaims2C`'s new conjunct asks, at `.fvar`, for
`∀ ρ, Sat2 V Δa ρ → AnnotOk2 V ρ tya`, where `tya` is the leaf's own
annotation and `t = ty` is the leaf's own type.  The clause's only
source for anything about `tya` is `CtxOk2`, and its leaf package has
exactly three conjuncts: **definedness** (`denote2 … = some tya`), the
**slot** (`Δa[d-1-l.1]? = some Aa`) and the **link**
(`interp2 ρ tya = interp2 (ρ ∘ (· + k + 1)) Aa`).  Truthfulness is not
among them, and it does not follow from the link: `AnnotOk2` is a
hereditary structural predicate, and an `interp2` *value* determines
nothing about it — that is the same wall `TypeOk2` was written to name.

So the generation-four extension is **free at `.sort` and `.bvar` and
not free at `.fvar`**, and the deficit is on the supplier side, in
this file's own `CtxOk2`.  The clause below takes the fact explicitly,
in exactly the shape a fourth `CtxOk2` conjunct would supply — the same
device, and for the same reason, as the sealed `infer_fvar_claim2`
above.  `CtxOk2Ann` names the proposed conjunct and the lemmas after it
check that it survives the kit; the change itself is a junction
decision, not a consumer's, because three quarters build on `CtxOk2`
concurrently. -/

/-! ### The proposed supplier, checked

`CtxOk2Ann` is the fourth leaf conjunct, stated **beside** `CtxOk2`
rather than inside it so that nothing built against the current
`CtxOk2` breaks while the junction decides.  What follows is the
evidence a strengthening is supposed to come with: it survives every
constructor in the kit, and it is inhabited beyond vacuity. -/

/-! ## The three dispatch clauses live in `Step2/InferQ.lean`

Re-pointed to `InferClaims2C` here *and* in the inference quarter,
simultaneously — the **fifth** collision of this campaign and the first
caused by the junction rather than by the workers: both briefs listed
these three clauses, so both quarters owned them.

The inference quarter's copies are kept because they are wired into
`inferStep2C_of`; these were unwired duplicates.  The two differed only
in how they package the missing truthfulness at `.fvar` — a per-call
`hokTy` premise here, the routed `CtxAnn2` residue there — and the
routed form is what the assembly consumes.

`CtxOk2Ann` below is retained: it is the same fact at the *predicate*
granularity rather than the residue's, and it carries the survival kit
(`fvar_leaf`, `of_subset`, `fuelMono`, `weakenTop`, `openCong`,
`openS`) that a fourth leaf conjunct would need.  Unifying it with
`CtxAnn2` is generation five's, alongside the conjunct itself. -/

/-- **The proposed fourth conjunct of `CtxOk2`.**  Quantified over
`tya` rather than carrying its own existential, so it composes with
`CtxOk2`'s package by `denote2`'s functionality. -/
def CtxOk2Ann {env : Env} (m : EnvS2UM V μ env) (μ : CheckMode)
    (φ : Name → Nat) (F d : Nat) (Δa : List AVExpr) (e : Expr) :
    Prop :=
  ∀ l ∈ e.fvarLeaves, ∀ tya : AVExpr,
    denote2 μ m.acval env φ F d l.2.2 = some tya →
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ tya

/-- What the `.fvar` clause takes, read off the proposed conjunct — so
`infer_fvar_claim2C`'s `hokTy` really is this and nothing more. -/
theorem CtxOk2Ann.fvar_leaf {F d idx : Nat} {Δa : List AVExpr}
    {n : Name} {ty : Expr}
    (hA : CtxOk2Ann m μ φ F d Δa (.fvar idx n ty)) :
    ∀ tya : AVExpr, denote2 μ m.acval env φ F d ty = some tya →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ tya :=
  hA (idx, n, ty) (by simp [Expr.fvarLeaves])

/-- Restriction, exactly as `CtxOk2.of_subset`. -/
theorem CtxOk2Ann.of_subset {F d : Nat} {Δa : List AVExpr}
    {e e' : Expr} (hA : CtxOk2Ann m μ φ F d Δa e)
    (hsub : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) :
    CtxOk2Ann m μ φ F d Δa e' :=
  fun l hl => hA l (hsub l hl)

/-- No leaves, nothing to say. -/
theorem CtxOk2Ann.of_fvarLeaves_nil {F d : Nat} {Δa : List AVExpr}
    {e : Expr} (h : e.fvarLeaves = []) :
    CtxOk2Ann m μ φ F d Δa e :=
  fun l hl => by rw [h] at hl; exact absurd hl (by simp)

/-- Fuel monotonicity, on the pair: the leaf's annotation at the
higher fuel *is* the one at the lower, by `denote2_fuelMono` and
functionality, so the grading transports unchanged. -/
theorem CtxOk2Ann.fuelMono {F F' d : Nat} {Δa : List AVExpr}
    {e : Expr} (hle : F ≤ F') (hC : CtxOk2 m μ φ F d Δa e)
    (hA : CtxOk2Ann m μ φ F d Δa e) :
    CtxOk2Ann m μ φ F' d Δa e := by
  intro l hl tya hden ρ hρ
  obtain ⟨-, -, tya₀, -, hden₀, -, -⟩ := hC.2 l hl
  have h' := denote2_fuelMono hle d l.2.2 hden₀
  rw [h'] at hden
  obtain rfl : tya₀ = tya := Option.some.inj hden
  exact hA l hl tya₀ hden₀ ρ hρ

/-- **Weakening by one binder.**  The leaf annotations lift, so the
grading is `AnnotOk2.hoist_lift` of the old one. -/
theorem CtxOk2Ann.weakenTop {F d : Nat} {Δa : List AVExpr}
    {Ba : AVExpr} {e : Expr} (hC : CtxOk2 m μ φ F d Δa e)
    (hA : CtxOk2Ann m μ φ F d Δa e) (hw : Expr.WScoped d e) :
    CtxOk2Ann m μ φ F (d + 1) (Ba :: Δa) e := by
  intro l hl tya hden
  obtain ⟨hlt, -, tya₀, -, hden₀, -, -⟩ := hC.2 l hl
  have hwl : Expr.WScoped d l.2.2 :=
    (Setlec.Expr.WScoped_leaves e hw l hl).2.mono (by omega)
  rw [denote2_weaken_top m.base.wf m.acval_closed hwl, hden₀] at hden
  obtain rfl : AVExpr.liftN 1 tya₀ 0 = tya := Option.some.inj hden
  exact AnnotOk2.hoist_lift (X := Ba) (hA l hl tya₀ hden₀)

/-- **Opening a binder congruence.**  The new leaf's annotation is the
*right* domain lifted, and its grading is `hok₂` — which
`CtxOk2.openCong` already takes and `DefEqClaims2C` already supplies as
one of its two hoisted premises.  So the proposed conjunct costs the
congruence sites **nothing new**: this is the self-propagation
argument, applied to the strengthening rather than to the claim. -/
theorem CtxOk2Ann.openCong {F d : Nat} {Δa : List AVExpr}
    {body ty : Expr} {n : Name} {ta₁ ta₂ : AVExpr}
    (hb : CtxOk2 m μ φ F d Δa body) (ht : CtxOk2 m μ φ F d Δa ty)
    (hAb : CtxOk2Ann m μ φ F d Δa body)
    (hAt : CtxOk2Ann m μ φ F d Δa ty)
    (hty : denote2 μ m.acval env φ F d ty = some ta₂)
    (hok₂ : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta₂) :
    CtxOk2Ann m μ φ F (d + 1) (ta₁ :: Δa)
      (body.instantiate1 (.fvar d n ty)) := by
  intro l hl tya hden
  rcases Setlec.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
  · exact CtxOk2Ann.weakenTop (Ba := ta₁) hb hAb hb.wScoped l hl'
      tya hden
  · rw [Setlec.Expr.fvarLeaves] at hl'
    rcases List.mem_cons.mp hl' with rfl | hl''
    · rw [denote2_weaken_top m.base.wf m.acval_closed ht.wScoped,
        hty] at hden
      obtain rfl : AVExpr.liftN 1 ta₂ 0 = tya := Option.some.inj hden
      exact AnnotOk2.hoist_lift (X := ta₁) hok₂
    · exact CtxOk2Ann.weakenTop (Ba := ta₁) ht hAt ht.wScoped l hl''
        tya hden

/-- The non-congruence opening: the same lemma at `ta₁ = ta₂`, which
is the shape `CtxOk2.openS`/`CtxOk2.open` produce. -/
theorem CtxOk2Ann.openS {F d : Nat} {Δa : List AVExpr}
    {body ty : Expr} {n : Name} {ta : AVExpr}
    (hb : CtxOk2 m μ φ F d Δa body) (ht : CtxOk2 m μ φ F d Δa ty)
    (hAb : CtxOk2Ann m μ φ F d Δa body)
    (hAt : CtxOk2Ann m μ φ F d Δa ty)
    (hty : denote2 μ m.acval env φ F d ty = some ta)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) :
    CtxOk2Ann m μ φ F (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d n ty)) :=
  CtxOk2Ann.openCong (ta₁ := ta) hb ht hAb hAt hty hok

/-- **Inhabited beyond vacuity**, the check a strengthening owes: at
depth `1` over a satisfiable context, with a real `fvar` leaf whose
annotation is a `Sort`.  (`CtxOk2Ann` at depth `0` is free for the same
reason `CtxOk2` is, so the depth-`0` witness would prove nothing.) -/
example (nm : Name) :
    CtxOk2Ann m μ φ 1 1 [AVExpr.sort 1]
      (.fvar 0 nm (.sort (.succ .zero))) := by
  intro l hl tya hden ρ _
  simp only [Setlec.Expr.fvarLeaves, List.mem_singleton] at hl
  subst hl
  rw [denote2] at hden
  obtain rfl : AVExpr.sort 1 = tya := Option.some.inj hden
  simp

end Amended

end Setlec.SetR.Interp2