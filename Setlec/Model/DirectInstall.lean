import Setlec.Model.DirectTower

/-!
# The direct simple-structure install: the constructed values

The install soundness of `checkDirectStruct` (`Setlec/Kernel/Checker.lean`,
task #82) rests on four hand-built values — the type former, the
constructor, the recursor and the projections — assembled from the
λ-tower builder (`Setlec/Model/DirectVal.lean`) and the dependent-pair
tower (`Setlec/Model/DirectTower.lean`):

    ⟦T⟧          = λ p⃗. Σ (x₀ ∈ ⟦F₀⟧) … {∗}
    ⟦T.mk⟧       = λ p⃗ f⃗. ⟨f₀, ⟨f₁, … ∗⟩⟩
    ⟦T.rec⟧      = λ p⃗ motive minor t. minor (proj₀ t) … (proj_{n-1} t)
    ⟦T.proj.i⟧   = λ p⃗ t. proj_i t

This module builds them and proves the facts the environment invariant
consumes.  Everything is stated over the *pre-block* environment and
valuation: the class is non-recursive (`directNonRec`), so every field
type already resolves there.

## The guard on the type former's body, and why it is not a hole

`⟦T⟧`'s body is `directTyBody`, the dependent-pair tower **guarded by
its own smallness** — the tower when it lands in `univ w`, the
singleton otherwise.  The guard exists because of the block's install
*order*, not because the tower might really be large:

* the type former is stored **first** (the constructor's type ends in
  `T p⃗`, so it neither resolves nor annotates before that), so the
  per-field universe bound has not been checked when `⟦T⟧` is fixed;
* the bound's semantic content (`FieldTele`) is read off
  `inferTypeCore`/`ensureSortCore` runs in the environment that already
  carries `T`, and turning those into interpretation facts needs an
  `EnvModel` of that environment — which is exactly what the type
  former's install is constructing.  Demanding the tower's smallness at
  the type former is therefore circular.

The junk branch is **unreachable on any block the checker accepts**:
`checkDirectCtor` checks the per-field universe bound
(`Inductive/Add.lean:225-228`), `FieldTele_of_walk` turns it into
`FieldTele`, and `sigmaTowerV_mem_univ` then says the tower *is* small,
so `directTyBody_eq` rewrites the guard away.  Every later member of
the block — the constructor, the recursor, the projections — has that
bound in scope and goes through `directTyBody_eq`; none of them can be
installed without it.  The guard is thus a construction-time
case split inside a value, never a runtime gate and never a weakening
of what the model asserts about an accepted block.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}
variable {cval : ConstVal V}

open SetTheory Expr

/-! ### Telescope shape bookkeeping -/

/-- `stripPis` commutes with `instantiate1` on the residual body. -/
theorem stripPis_instantiate1_body :
    ∀ (k : Nat) (e v : Expr) (j : Nat) (bs : List (Name × Expr × BinderMeta))
      (b : Expr), Expr.stripPis k e = some (bs, b) →
      ∃ bs', Expr.stripPis k (e.instantiate1 v j) =
        some (bs', b.instantiate1 v (j + k)) := by
  intro k
  induction k with
  | zero =>
    intro e v j bs b h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], by simp [Expr.stripPis]⟩
  | succ k ih =>
    intro e v j bs b h
    match e with
    | .forallE n ty body m =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs0, b0⟩, hp, hpe⟩ := h
      simp only [Prod.mk.injEq] at hpe
      obtain ⟨-, rfl⟩ := hpe
      obtain ⟨bs', hbs'⟩ := ih body v (j + 1) bs0 b0 hp
      have hj : j + 1 + k = j + (k + 1) := by omega
      rw [hj] at hbs'
      refine ⟨(n, ty.instantiate1 v j, m) :: bs', ?_⟩
      rw [Expr.instantiate1, Expr.stripPis, hbs']
      rfl
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      exact nomatch h

omit [SetTheory V] in
/-- Opening a telescope splits at any prefix: the first `a` variables
are the prefix opening's, and the rest open the residual from the
shifted base. -/
theorem openPisAtFvars_add :
    ∀ (a b : Nat) {e : Expr} (i₀ : Nat) {fvs : List Expr} {rest : Expr},
      openPisAtFvars (a + b) e i₀ = some (fvs, rest) →
      ∃ mid, openPisAtFvars a e i₀ = some (fvs.take a, mid) ∧
        openPisAtFvars b mid (i₀ + a) = some (fvs.drop a, rest) := by
  intro a
  induction a with
  | zero =>
    intro b e i₀ fvs rest h
    exact ⟨e, by simp [openPisAtFvars], by simpa using h⟩
  | succ a ih =>
    intro b e i₀ fvs rest h
    rw [show a + 1 + b = (a + b) + 1 from by omega] at h
    match e with
    | .forallE n dom body m =>
      simp only [openPisAtFvars] at h
      cases hrec : openPisAtFvars (a + b)
          (body.instantiate1 (.fvar i₀ n dom)) (i₀ + 1) with
      | none => rw [hrec] at h; exact nomatch h
      | some q =>
        rw [hrec] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨mid, h1, h2⟩ := ih b (i₀ + 1) hrec
        refine ⟨mid, ?_, ?_⟩
        · simp only [openPisAtFvars, List.take_succ_cons, h1]
        · rw [show i₀ + (a + 1) = i₀ + 1 + a from by omega]
          simpa using h2
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      simp only [openPisAtFvars] at h; exact nomatch h

/-- A telescope ending in a `Sort` opens to that very sort: the residual
of any fitting walk of the right length is `.sort s`. -/
theorem TeleFit_rest_sort :
    ∀ (k : Nat) {d : Nat} {ρ : Nat → V} {ty : Expr} {xs : List V}
      {d' : Nat} {ρ' : Nat → V} {rest : Expr} {s : Level}
      {bs : List (Name × Expr × BinderMeta)},
      TeleFit V cval env φ d ρ ty xs d' ρ' rest → xs.length = k →
      Expr.stripPis k ty = some (bs, .sort s) → rest = .sort s := by
  intro k
  induction k with
  | zero =>
    intro d ρ ty xs d' ρ' rest s bs hfit hlen hstrip
    obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero hlen
    cases hfit
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hstrip
    exact hstrip.2
  | succ k ih =>
    intro d ρ ty xs d' ρ' rest s bs hfit hlen hstrip
    cases hfit with
    | nil => exact absurd hlen (by simp)
    | @cons d ρ n dom body m x xs d₂ ρ₂ rest A hdom hx hfit =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hstrip
      obtain ⟨⟨bs0, b0⟩, hp, hpe⟩ := hstrip
      simp only [Prod.mk.injEq] at hpe
      obtain ⟨-, rfl⟩ := hpe
      obtain ⟨bs', hbs'⟩ := stripPis_instantiate1_body k body
        (.fvar d n dom) 0 bs0 (.sort s) hp
      rw [Expr.instantiate1] at hbs'
      exact ih hfit (by simpa using hlen) hbs'

/-- A fitting walk of length `k` lands exactly where `openPisAtFvars`
does: both open the telescope at `fvar d, fvar (d+1), …` carrying the
binders' own names and domains. -/
theorem TeleFit_open :
    ∀ (k : Nat) {d : Nat} {ρ : Nat → V} {ty : Expr} {xs : List V}
      {d' : Nat} {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ d ρ ty xs d' ρ' rest → xs.length = k →
      d' = d + k ∧ ∃ fvs, openPisAtFvars k ty d = some (fvs, rest) := by
  intro k
  induction k with
  | zero =>
    intro d ρ ty xs d' ρ' rest hfit hlen
    obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero hlen
    cases hfit
    exact ⟨rfl, [], rfl⟩
  | succ k ih =>
    intro d ρ ty xs d' ρ' rest hfit hlen
    cases hfit with
    | nil => exact absurd hlen (by simp)
    | @cons d ρ n dom body m x xs d₂ ρ₂ rest A hdom hx hfit =>
      obtain ⟨hd, fvs, hopen⟩ := ih hfit (by simpa using hlen)
      refine ⟨by omega, Expr.fvar d n dom :: fvs, ?_⟩
      rw [openPisAtFvars, hopen]

/-- An empty value spine leaves the frame and the telescope alone.
(Stated as a lemma because `cases` on the fit cannot refute the `cons`
constructor when the telescope is a stuck `instantiate1`.) -/
theorem TeleFit_nil_eq {d : Nat} {ρ : Nat → V} {e : Expr} {d' : Nat}
    {ρ' : Nat → V} {rest : Expr}
    (h : TeleFit V cval env φ d ρ e [] d' ρ' rest) :
    d' = d ∧ ρ' = ρ ∧ rest = e := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- A fitting walk splits at any point. -/
theorem TeleFit_split :
    ∀ {d : Nat} {ρ : Nat → V} {ty : Expr} {xs ys : List V}
      {d' : Nat} {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ d ρ ty (xs ++ ys) d' ρ' rest →
      ∃ d₁ ρ₁ mid, TeleFit V cval env φ d ρ ty xs d₁ ρ₁ mid ∧
        TeleFit V cval env φ d₁ ρ₁ mid ys d' ρ' rest := by
  intro d ρ ty xs
  induction xs generalizing d ρ ty with
  | nil => intro ys d' ρ' rest hfit; exact ⟨d, ρ, ty, TeleFit.nil, hfit⟩
  | cons x xs ih =>
    intro ys d' ρ' rest hfit
    cases hfit with
    | @cons d ρ n dom body m x' xs' d₂ ρ₂ rest A hdom hx hfit =>
      obtain ⟨d₁, ρ₁, mid, h1, h2⟩ := ih hfit
      exact ⟨d₁, ρ₁, mid, TeleFit.cons hdom hx h1, h2⟩

/-- Fitting walks compose. -/
theorem TeleFit_append :
    ∀ {d : Nat} {ρ : Nat → V} {ty : Expr} {xs : List V} {d₁ : Nat}
      {ρ₁ : Nat → V} {mid : Expr} {ys : List V} {d' : Nat} {ρ' : Nat → V}
      {rest : Expr},
      TeleFit V cval env φ d ρ ty xs d₁ ρ₁ mid →
      TeleFit V cval env φ d₁ ρ₁ mid ys d' ρ' rest →
      TeleFit V cval env φ d ρ ty (xs ++ ys) d' ρ' rest := by
  intro d ρ ty xs d₁ ρ₁ mid ys d' ρ' rest h₁
  induction h₁ with
  | nil => exact fun h => h
  | @cons d ρ n dom body mb x xs d₂ ρ₂ mid A hdom hx h ih =>
    exact fun h₂ => TeleFit.cons hdom hx (ih h₂)

/-- A fitting walk keeps interpretability and annotation truthfulness:
the residual of an interpretable, truthfully annotated telescope is
itself interpretable and truthfully annotated.  (Unlike `TeleFit.elim`
this needs no inhabitant of the telescope — the fibre facts come from
`AnnotOk`'s `forallE` clause alone, which is what makes it usable at a
*type* that is being installed.) -/
theorem TeleFit_interp_rest :
    ∀ {d : Nat} {ρ : Nat → V} {ty : Expr} {xs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ d ρ ty xs d' ρ' rest →
      AnnotOk V cval env φ d ρ ty →
      (∃ P, interpExpr V cval env φ d ρ ty = some P) →
      (∃ Q, interpExpr V cval env φ d' ρ' rest = some Q) ∧
        AnnotOk V cval env φ d' ρ' rest := by
  intro d ρ ty xs d' ρ' rest hfit
  induction hfit with
  | nil => intro hA hi; exact ⟨hi, hA⟩
  | @cons d ρ n dom body m x xs d₂ ρ₂ rest A hdom hx hfit ih =>
    intro hA _
    simp only [AnnotOk] at hA
    obtain ⟨-, ⟨cod, hcod⟩, hcond⟩ := hA
    obtain ⟨hAb, hwfact⟩ := hcond x A hdom hx
    obtain ⟨w, hwi, -⟩ := hwfact cod hcod
    exact ih hAb ⟨w, hwi⟩

/-! ### The type former's value -/

/-- The constructor's field telescope: the residual of the
constructor's **own** parameter opening (junk outside the class).

That opening is the block's one frame.  It is where every value-spine
fit of the constructor's type at the canonical frame lands
(`TeleFit_open`), so the field types carry exactly the annotations the
walks produce, and `checkDirectCtor` runs the per-field universe walk
over this very residual. -/
def directCRest (cty : Expr) (nP : Nat) : Expr :=
  match openPisAtFvars nP cty 0 with
  | some (_, crest) => crest
  | none => .sort .zero

/-- The type former's body value at one parameter instantiation: the
dependent-pair tower over the field telescope, **guarded by its own
smallness**.

*Why the guard* (a shape finding of the install order, DESIGN.md).  The
type former is stored *first* — the constructor's type mentions it, so
it does not resolve before the block — and only then is the
constructor's type annotated and the per-field universe bound checked.
The bound's semantic content (`FieldTele`) is therefore not available
at the type former's own install: it is read off checks that run in the
*extended* environment, whose model is what the type former's install
is constructing.  The guard breaks that circularity: `⟦T⟧`'s membership
in its type is unconditional, and every later member of the block —
which does have the bound in scope — discharges the guard and sees the
plain tower (`directTyBody_eq`).  The junk branch is unreachable on any
block the checker accepts. -/
noncomputable def directTyBody (V : Type u) [SetTheory V] (cval : ConstVal V)
    (env : Env) (ψ : Name → Nat) (w nF d : Nat) (ρ : Nat → V) (crest : Expr) :
    V :=
  open Classical in
  if sigmaTowerV V cval env ψ w nF d ρ crest ∈ˢ (univ w : V) then
    sigmaTowerV V cval env ψ w nF d ρ crest
  else unitSet

/-- The guarded body is always small — the point of the guard. -/
theorem directTyBody_mem_univ {ψ : Name → Nat} {w nF d : Nat} {ρ : Nat → V}
    {crest : Expr} :
    directTyBody V cval env ψ w nF d ρ crest ∈ˢ (univ w : V) := by
  unfold directTyBody
  split
  · assumption
  · exact unitSet_mem_univ w

/-- Under the checked per-field universe bound the guard is discharged:
the type former's body *is* the dependent-pair tower. -/
theorem directTyBody_eq {ψ : Name → Nat} {w nF d : Nat} {ρ : Nat → V}
    {crest : Expr} (hfld : FieldTele V cval env ψ w nF d ρ crest) :
    directTyBody V cval env ψ w nF d ρ crest =
      sigmaTowerV V cval env ψ w nF d ρ crest := by
  unfold directTyBody
  rw [if_pos (sigmaTowerV_mem_univ hfld)]

/-- `⟦T⟧`: the λ-tower over the parameter telescope whose body is the
(guarded) dependent-pair tower over the field telescope. -/
noncomputable def directTyVal (V : Type u) [SetTheory V] (cval : ConstVal V)
    (env : Env) (tty cty : Expr) (nP nF : Nat) (s : Level)
    (ψ : Name → Nat) : V :=
  teleLamV V cval env ψ nP 0 (rho0 V) tty
    (fun d ρ _ => directTyBody V cval env ψ (s.eval ψ) nF d ρ
      (directCRest cty nP))

/-- The type former's value inhabits the interpretation of its type.
Unconditional: the guard supplies the smallness the type's result sort
demands, so this holds at the type former's own install, before the
per-field universe bound has been checked. -/
theorem directTyVal_mem {tty cty : Expr} {nP nF : Nat} {s : Level} {Tv : V}
    {bs : List (Name × Expr × BinderMeta)}
    (hstrip : Expr.stripPis nP tty = some (bs, .sort s))
    (htyI : interpExpr V cval env φ 0 (rho0 V) tty = some Tv)
    (htyA : AnnotOk V cval env φ 0 (rho0 V) tty) :
    directTyVal V cval env tty cty nP nF s φ ∈ˢ Tv := by
  refine teleLamV_mem nP (by rw [hstrip]; rfl) htyI htyA ?_
  intro ps d ρ rest hfit hlen
  obtain rfl : rest = Expr.sort s := TeleFit_rest_sort nP hfit hlen hstrip
  exact ⟨univ (s.eval φ), by rw [interpExpr], directTyBody_mem_univ⟩

/-- Applying the type former's value to a fitting parameter spine
computes the dependent-pair tower — the equation every later step goes
through (`⟦T p⃗⟧` *is* the tower). -/
theorem directTyVal_fold {tty cty : Expr} {nP nF : Nat} {s : Level}
    {ps : List V} {d' : Nat} {ρ' : Nat → V}
    {bs : List (Name × Expr × BinderMeta)}
    (hstrip : Expr.stripPis nP tty = some (bs, .sort s))
    (htyA : AnnotOk V cval env φ 0 (rho0 V) tty)
    (hfit : TeleFit V cval env φ 0 (rho0 V) tty ps d' ρ' (.sort s))
    (hlen : ps.length = nP)
    -- only at *this* spine: the λ-tower's own body obligation is
    -- discharged unconditionally by the guard (`directTyBody_mem_univ`),
    -- so the checked universe bound is needed exactly where the guard
    -- is finally removed
    (hfield : FieldTele V cval env φ (s.eval φ) nF d' ρ' (directCRest cty nP)) :
    SpineFold V (directTyVal V cval env tty cty nP nF s φ) ps =
      sigmaTowerV V cval env φ (s.eval φ) nF d' ρ' (directCRest cty nP) := by
  rw [directTyVal, teleLamV_fold (S := fun d ρ _ =>
      directTyBody V cval env φ (s.eval φ) nF d ρ (directCRest cty nP))
    (by rw [hstrip]; rfl) hfit hlen htyA
    (fun xs d₂ ρ₂ rest hfit₂ hlen₂ =>
      ⟨univ (s.eval φ), by rw [TeleFit_rest_sort nP hfit₂ hlen₂ hstrip,
        interpExpr], directTyBody_mem_univ⟩)]
  exact directTyBody_eq hfield

/-- A field-free direct structure is unit-like: its model is the
singleton, so any two members of the interpreted family coincide.  This
is what the `unitlike := nF == 0` capability rests on. -/
theorem directTyVal_unitlike {tty cty : Expr} {nP : Nat} {s : Level}
    {ps : List V} {d' : Nat} {ρ' : Nat → V} {x y : V}
    {bs : List (Name × Expr × BinderMeta)}
    (hstrip : Expr.stripPis nP tty = some (bs, .sort s))
    (htyA : AnnotOk V cval env φ 0 (rho0 V) tty)
    (hfit : TeleFit V cval env φ 0 (rho0 V) tty ps d' ρ' (.sort s))
    (hlen : ps.length = nP)
    (hx : x ∈ˢ SpineFold V (directTyVal V cval env tty cty nP 0 s φ) ps)
    (hy : y ∈ˢ SpineFold V (directTyVal V cval env tty cty nP 0 s φ) ps) :
    x = y := by
  have hfold := directTyVal_fold (cty := cty) (nF := 0) hstrip htyA hfit hlen
    trivial
  rw [hfold] at hx hy
  rw [mem_unitSet_iff.mp hx, mem_unitSet_iff.mp hy]

/-! ### Moving the constructed values across the block's own extensions

The type former's value is fixed over the **pre-block** pair
(`m.val`, `env`) — it is installed first — while the constructor's, the
recursor's and the projections' obligations are stated over the pair of
*their own* install, which is the pre-block environment plus the block
members stored so far.  The values in between have to be recognised as
the same object.

They are, and for a reason that is local: the λ-tower and the
dependent-pair tower read the telescope **only through its binder
domains' interpretations** (plus the binders' own codomain-sort tags,
which are syntax).  The block's field domains resolve before the block
(`directNonRec` for the raw ones, re-checked on the annotated ones in
`checkDirectCtor`), so their interpretations do not move.

The frame is not generalized: `teleLamV k d` evaluates its body at
exactly `d + k`, so the tower is only ever read at the frame the
install's own `openPisAtFvars` runs at. -/

/-- Two (valuation, environment) pairs that interpret every expression
resolving in the **first** environment alike.  Established between the
pre-block pair and any later one by `interp_mono` (the environment only
grows by fresh constants) and `interp_cval_ext` (the valuations agree
on stored names). -/
def InterpAgree (V : Type u) [SetTheory V] (cval₁ : ConstVal V) (env₁ : Env)
    (cval₂ : ConstVal V) (env₂ : Env) (φ : Name → Nat) : Prop :=
  ∀ (e : Expr), e.constsResolve env₁ = true → ∀ (d : Nat) (ρ : Nat → V),
    interpExpr V cval₁ env₁ φ d ρ e = interpExpr V cval₂ env₂ φ d ρ e

variable {cval₁ cval₂ : ConstVal V} {env₁ env₂ : Env}

/-- The dependent-pair tower only reads the field domains. -/
theorem sigmaTowerV_congr (h : InterpAgree V cval₁ env₁ cval₂ env₂ φ)
    {w : Nat} :
    ∀ (k d : Nat) (ρ : Nat → V) (ty : Expr) (fvs : List Expr) (rest : Expr),
      openPisAtFvars k ty d = some (fvs, rest) →
      (∀ x ∈ fvs, (Expr.fvarTypeD x).constsResolve env₁ = true) →
      sigmaTowerV V cval₁ env₁ φ w k d ρ ty =
        sigmaTowerV V cval₂ env₂ φ w k d ρ ty := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _; rfl
  | succ k ih =>
    intro d ρ ty fvs rest hop hfvs
    match ty with
    | .forallE n dom body mb =>
      simp only [openPisAtFvars] at hop
      cases hrec : openPisAtFvars k (body.instantiate1 (.fvar d n dom)) (d + 1) with
      | none => rw [hrec] at hop; exact nomatch hop
      | some q =>
        rw [hrec] at hop
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have hdom : dom.constsResolve env₁ = true :=
          hfvs _ List.mem_cons_self
        rw [sigmaTowerV_forallE, sigmaTowerV_forallE, h dom hdom d ρ]
        refine congrArg _ (funext fun x => ?_)
        exact ih (d + 1) (updV V ρ d x) _ q.1 q.2 hrec
          (fun y hy => hfvs y (List.mem_cons_of_mem _ hy))
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      exact nomatch hop

/-- The per-field universe bound only reads the field domains. -/
theorem FieldTele_congr (h : InterpAgree V cval₁ env₁ cval₂ env₂ φ)
    {w : Nat} :
    ∀ (k d : Nat) (ρ : Nat → V) (ty : Expr) (fvs : List Expr) (rest : Expr),
      openPisAtFvars k ty d = some (fvs, rest) →
      (∀ x ∈ fvs, (Expr.fvarTypeD x).constsResolve env₁ = true) →
      FieldTele V cval₁ env₁ φ w k d ρ ty →
      FieldTele V cval₂ env₂ φ w k d ρ ty := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _; trivial
  | succ k ih =>
    intro d ρ ty fvs rest hop hfvs hfld
    match ty with
    | .forallE n dom body mb =>
      simp only [openPisAtFvars] at hop
      cases hrec : openPisAtFvars k (body.instantiate1 (.fvar d n dom)) (d + 1) with
      | none => rw [hrec] at hop; exact nomatch hop
      | some q =>
        rw [hrec] at hop
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨A, hA, hAu, hrest⟩ := hfld
        have hdom : dom.constsResolve env₁ = true :=
          hfvs _ List.mem_cons_self
        refine ⟨A, by rw [← h dom hdom d ρ]; exact hA, hAu, ?_⟩
        intro x hx
        exact ih (d + 1) (updV V ρ d x) _ q.1 q.2 hrec
          (fun y hy => hfvs y (List.mem_cons_of_mem _ hy)) (hrest x hx)
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ => exact hfld.elim

/-- **A value-spine fit crosses the block's own extensions.**  The fit
reads its telescope only through the domains' interpretations, which
`InterpAgree` preserves for anything resolving in the smaller
environment — so a fit at the *later* model transports back to the
earlier one, which is what lets a stage fact proved at one install
be consumed at the next. -/
theorem TeleFit_congr (h : InterpAgree V cval₁ env₁ cval₂ env₂ φ) :
    ∀ {d : Nat} {ρ : Nat → V} {ty : Expr} {vs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval₂ env₂ φ d ρ ty vs d' ρ' rest →
      ty.constsResolve env₁ = true →
      TeleFit V cval₁ env₁ φ d ρ ty vs d' ρ' rest := by
  intro d ρ ty vs d' ρ' rest hfit
  induction hfit with
  | nil => intro _; exact TeleFit.nil
  | @cons d ρ n ty0 body mb x xs d' ρ' rest A hity hx hfit ih =>
    intro hres
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    exact TeleFit.cons (by rw [h ty0 hres.1 d ρ]; exact hity) hx
      (ih (Expr.constsResolve_instantiate1
        (by simpa [Expr.constsResolve] using hres.1) 0 hres.2))

/-- The forward direction of `TeleFit_congr`. -/
theorem TeleFit_congr' (h : InterpAgree V cval₁ env₁ cval₂ env₂ φ) :
    ∀ {d : Nat} {ρ : Nat → V} {ty : Expr} {vs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval₁ env₁ φ d ρ ty vs d' ρ' rest →
      ty.constsResolve env₁ = true →
      TeleFit V cval₂ env₂ φ d ρ ty vs d' ρ' rest := by
  intro d ρ ty vs d' ρ' rest hfit
  induction hfit with
  | nil => intro _; exact TeleFit.nil
  | @cons d ρ n ty0 body mb x xs d' ρ' rest A hity hx hfit ih =>
    intro hres
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    exact TeleFit.cons (by rw [← h ty0 hres.1 d ρ]; exact hity) hx
      (ih (Expr.constsResolve_instantiate1
        (by simpa [Expr.constsResolve] using hres.1) 0 hres.2))

/-- The guarded body follows the tower. -/
theorem directTyBody_congr (h : InterpAgree V cval₁ env₁ cval₂ env₂ φ)
    {w nF d : Nat} {ρ : Nat → V} {crest : Expr} {fvs : List Expr}
    {rest : Expr} (hop : openPisAtFvars nF crest d = some (fvs, rest))
    (hfvs : ∀ x ∈ fvs, (Expr.fvarTypeD x).constsResolve env₁ = true) :
    directTyBody V cval₁ env₁ φ w nF d ρ crest =
      directTyBody V cval₂ env₂ φ w nF d ρ crest := by
  unfold directTyBody
  rw [sigmaTowerV_congr h nF d ρ crest fvs rest hop hfvs]

/-- The λ-tower only reads the telescope's binder domains, and only
evaluates its body at the frame `d + k` it ends at. -/
theorem teleLamV_congr (h : InterpAgree V cval₁ env₁ cval₂ env₂ φ) :
    ∀ (k d : Nat) (ρ : Nat → V) (ty : Expr)
      (S₁ S₂ : Nat → (Nat → V) → List V → V),
      ty.constsResolve env₁ = true →
      (∀ ρ' xs, S₁ (d + k) ρ' xs = S₂ (d + k) ρ' xs) →
      teleLamV V cval₁ env₁ φ k d ρ ty S₁ =
        teleLamV V cval₂ env₂ φ k d ρ ty S₂ := by
  intro k
  induction k with
  | zero =>
    intro d ρ ty S₁ S₂ _ hS
    simpa using hS ρ []
  | succ k ih =>
    intro d ρ ty S₁ S₂ hres hS
    match ty with
    | .forallE n dom body mb =>
      simp only [Expr.constsResolve, Bool.and_eq_true] at hres
      rw [teleLamV_forallE, teleLamV_forallE, h dom hres.1 d ρ]
      refine congrArg _ (funext fun x => ?_)
      refine ih (d + 1) (updV V ρ d x) _ _ _
        (Expr.constsResolve_instantiate1 (by simpa [Expr.constsResolve] using hres.1)
          0 hres.2)
        (fun ρ' xs => ?_)
      have := hS ρ' (x :: xs)
      rw [show d + 1 + k = d + (k + 1) from by omega]
      exact this
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

/-- The type former's value is the same object at every later install
of its own block. -/
theorem directTyVal_congr (h : InterpAgree V cval₁ env₁ cval₂ env₂ φ)
    {tty cty : Expr} {nP nF : Nat} {s : Level} {fvs : List Expr}
    {rest : Expr}
    (htres : tty.constsResolve env₁ = true)
    (hop : openPisAtFvars nF (directCRest cty nP) nP = some (fvs, rest))
    (hfvs : ∀ x ∈ fvs, (Expr.fvarTypeD x).constsResolve env₁ = true) :
    directTyVal V cval₁ env₁ tty cty nP nF s φ =
      directTyVal V cval₂ env₂ tty cty nP nF s φ := by
  unfold directTyVal
  refine teleLamV_congr h nP 0 (rho0 V) tty _ _ htres (fun ρ' xs => ?_)
  simpa using directTyBody_congr h hop hfvs

/-! ### The constructor's value -/

/-- `⟦T.mk⟧`: the λ-tower over the constructor's telescope whose body is
the tuple of the *field* values. -/
noncomputable def directCtorVal (V : Type u) [SetTheory V] (cval : ConstVal V)
    (env : Env) (cty : Expr) (nP nF : Nat) (ψ : Name → Nat) : V :=
  teleLamV V cval env ψ (nP + nF) 0 (rho0 V) cty
    (fun _ _ xs => tupleV (xs.drop nP))

/-- The constructor's λ-tower body obligation.  The two hypotheses are
what the install establishes: the field telescope is a `FieldTele` at
every parameter instantiation (the universe bound), and the
constructor's residual — the type former applied to exactly the
parameters — interprets to the very tower that `⟦T⟧` unfolds to at
those parameters. -/
theorem directCtorVal_body {cty : Expr} {nP nF w : Nat}
    (hw : w ≠ 0)
    (hfield : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (mid : Expr),
      TeleFit V cval env φ 0 (rho0 V) cty ps d₁ ρ₁ mid → ps.length = nP →
      FieldTele V cval env φ w nF d₁ ρ₁ mid)
    (hresid : ∀ (ps fs : List V) (d₁ : Nat) (ρ₁ : Nat → V) (mid : Expr)
      (d' : Nat) (ρ' : Nat → V) (rest : Expr),
      TeleFit V cval env φ 0 (rho0 V) cty ps d₁ ρ₁ mid → ps.length = nP →
      TeleFit V cval env φ d₁ ρ₁ mid fs d' ρ' rest → fs.length = nF →
      interpExpr V cval env φ d' ρ' rest =
        some (sigmaTowerV V cval env φ w nF d₁ ρ₁ mid)) :
    TeleBody V cval env φ (nP + nF) 0 (rho0 V) cty
      (fun _ _ xs => tupleV (xs.drop nP)) := by
  intro xs d' ρ' rest hfit hlen
  have hxs : xs = xs.take nP ++ xs.drop nP := (List.take_append_drop nP xs).symm
  rw [hxs] at hfit
  obtain ⟨d₁, ρ₁, mid, h1, h2⟩ := TeleFit_split hfit
  have hlp : (xs.take nP).length = nP := by
    rw [List.length_take]; omega
  have hlf : (xs.drop nP).length = nF := by
    rw [List.length_drop, hlen]; omega
  refine ⟨_, hresid _ _ _ _ _ _ _ _ h1 hlp h2 hlf, ?_⟩
  exact tupleV_mem hw (hfield _ _ _ _ h1 hlp) h2 hlf

/-- The constructor's value inhabits the interpretation of its type. -/
theorem directCtorVal_mem {cty : Expr} {nP nF : Nat} {Cv : V}
    (hstrip : (Expr.stripPis (nP + nF) cty).isSome = true)
    (hctyI : interpExpr V cval env φ 0 (rho0 V) cty = some Cv)
    (hctyA : AnnotOk V cval env φ 0 (rho0 V) cty)
    (hbody : TeleBody V cval env φ (nP + nF) 0 (rho0 V) cty
      (fun _ _ xs => tupleV (xs.drop nP))) :
    directCtorVal V cval env cty nP nF φ ∈ˢ Cv :=
  teleLamV_mem (nP + nF) hstrip hctyI hctyA hbody

/-- Applying the constructor's value along a fitting spine computes the
tuple of the field values — the equation the recursor's minor premise
goes through (`motive (C p⃗ f⃗)` *is* `motive (tupleV f⃗)`). -/
theorem directCtorVal_fold {cty : Expr} {nP nF : Nat} {xs : List V}
    {d' : Nat} {ρ' : Nat → V} {rest : Expr}
    (hstrip : (Expr.stripPis (nP + nF) cty).isSome = true)
    (hctyA : AnnotOk V cval env φ 0 (rho0 V) cty)
    (hfit : TeleFit V cval env φ 0 (rho0 V) cty xs d' ρ' rest)
    (hlen : xs.length = nP + nF)
    (hbody : TeleBody V cval env φ (nP + nF) 0 (rho0 V) cty
      (fun _ _ xs => tupleV (xs.drop nP))) :
    SpineFold V (directCtorVal V cval env cty nP nF φ) xs =
      tupleV (xs.drop nP) :=
  teleLamV_fold hstrip hfit hlen hctyA hbody

/-- The constructor's value is the same object at every later install
of its own block. -/
theorem directCtorVal_congr (h : InterpAgree V cval₁ env₁ cval₂ env₂ φ)
    {cty : Expr} {nP nF : Nat} (hcres : cty.constsResolve env₁ = true) :
    directCtorVal V cval₁ env₁ cty nP nF φ =
      directCtorVal V cval₂ env₂ cty nP nF φ :=
  teleLamV_congr h (nP + nF) 0 (rho0 V) cty _ _ hcres (fun _ _ => rfl)

/-! ### The projections' and the recursor's values -/

/-- `⟦T.proj.i⟧`: the λ-tower over `∀ p⃗ (t : T p⃗), F_i[…]` returning
field `i` of the subject. -/
noncomputable def directProjVal (V : Type u) [SetTheory V] (cval : ConstVal V)
    (env : Env) (pty : Expr) (nP i : Nat) (ψ : Name → Nat) : V :=
  teleLamV V cval env ψ (nP + 1) 0 (rho0 V) pty
    (fun _ _ xs => projV i (xs.getD nP SetTheory.empty))

/-- `⟦T.rec⟧`: the λ-tower over the recursor's telescope returning the
minor premise applied to the major's projections. -/
noncomputable def directRecVal (V : Type u) [SetTheory V] (cval : ConstVal V)
    (env : Env) (rty : Expr) (nP nF : Nat) (ψ : Name → Nat) : V :=
  teleLamV V cval env ψ (nP + 3) 0 (rho0 V) rty
    (fun _ _ xs => SpineFold V (xs.getD (nP + 1) SetTheory.empty)
      ((List.range nF).map fun j =>
        projV j (xs.getD (nP + 2) SetTheory.empty)))

/-! ### The iota equations, at the value level

These are the two facts the stored rules' fold obligation reduces to
once the λ-towers are folded away (`teleLamV_fold`): the recursor
applied to a constructor spine is the minor premise applied to the
fields, and a projection applied to a constructor spine is that field.
Both are `projV_tupleV` in disguise. -/

/-- Reading a list back off its own indices. -/
theorem map_range_getD :
    ∀ xs : List V,
      (List.range xs.length).map (fun j => xs.getD j SetTheory.empty) = xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congrArg (a :: ·) ?_
    have hfun : ((fun j => (a :: as).getD j SetTheory.empty) ∘ Nat.succ) =
        (fun j => as.getD j SetTheory.empty) := rfl
    rw [hfun]
    exact ih

/-- Field `i` of a tuple of `nF` values is the `i`-th value. -/
theorem directProj_iota {i nF : Nat} {fs : List V}
    (hlen : fs.length = nF) (hi : i < nF) :
    projV i (tupleV fs) = fs.getD i SetTheory.empty :=
  projV_tupleV i fs (by omega)

/-- The recursor's body on a constructor spine is the minor premise
applied to the very fields. -/
theorem directRec_iota {nF : Nat} {mi : V} {fs : List V}
    (hlen : fs.length = nF) :
    SpineFold V mi ((List.range nF).map fun j => projV j (tupleV fs)) =
      SpineFold V mi fs := by
  congr 1
  have : ((List.range nF).map fun j => projV j (tupleV fs)) =
      (List.range nF).map fun j => fs.getD j SetTheory.empty := by
    refine List.map_congr_left ?_
    intro j hj
    exact projV_tupleV j fs (by rw [hlen]; exact List.mem_range.mp hj)
  rw [this, ← hlen, map_range_getD]

/-- **The recursor's typing, semantically.**  A member `x` of the tower
is the tuple of its own projections (`sigmaTowerV_split`, structure
eta), and those projections fit the field telescope — so the minor
premise applied to them lands in `motive` of the reconstructed
constructor spine, which *is* `motive x`.  This is exactly why the
eliminator's conclusion `motive t` is reachable from the minor
premise's `motive (C p⃗ f⃗)`, with no `_model` theorem involved. -/
theorem directRec_body_mem {w nF d₁ : Nat} {ρ₁ : Nat → V} {mid : Expr}
    {x mi : V} {M : V → V}
    (hw : w ≠ 0)
    (hfld : FieldTele V cval env φ w nF d₁ ρ₁ mid)
    (hx : x ∈ˢ sigmaTowerV V cval env φ w nF d₁ ρ₁ mid)
    (hmi : ∀ (fs : List V) (d' : Nat) (ρ' : Nat → V) (rest : Expr),
      TeleFit V cval env φ d₁ ρ₁ mid fs d' ρ' rest → fs.length = nF →
      SpineFold V mi fs ∈ˢ M (tupleV fs)) :
    SpineFold V mi ((List.range nF).map fun j => projV j x) ∈ˢ M x := by
  obtain ⟨d', ρ', rest, hfit, htup⟩ := sigmaTowerV_split hw hfld hx
  have h := hmi _ d' ρ' rest hfit (by simp)
  rw [htup] at h
  exact h

/-- **A projection's typing, semantically.**  Field `i` of a member of
the tower inhabits the `i`-th domain of the field telescope,
instantiated at the earlier projections — which is what the generated
projection type (`directProjTy`) spells.

The fitting spine is the **canonical** one, `(range nF).map (projV · x)`
(`sigmaTowerV_split`, structure eta): the general "at every fitting
spine" form is *false* here, since the generated type substitutes the
subject's own projections and an unrelated fitting spine need not agree
with them. -/
theorem directProj_body_mem {w nF d₁ : Nat} {ρ₁ : Nat → V} {mid : Expr}
    {x : V} {i : Nat} {Q : V}
    (hw : w ≠ 0) (hi : i < nF)
    (hfld : FieldTele V cval env φ w nF d₁ ρ₁ mid)
    (hx : x ∈ˢ sigmaTowerV V cval env φ w nF d₁ ρ₁ mid)
    (hdom : ∀ (d' : Nat) (ρ' : Nat → V) (rest : Expr),
      TeleFit V cval env φ d₁ ρ₁ mid
        ((List.range nF).map fun j => projV j x) d' ρ' rest →
      ((List.range nF).map fun j => projV j x).getD i SetTheory.empty ∈ˢ Q) :
    projV i x ∈ˢ Q := by
  obtain ⟨d', ρ', rest, hfit, -⟩ := sigmaTowerV_split hw hfld hx
  have h := hdom d' ρ' rest hfit
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi] at h
  exact h

/-- `⟦T.proj.i⟧` inhabits the interpretation of its (generated) type. -/
theorem directProjVal_mem {pty : Expr} {nP i : Nat} {Pv : V}
    (hstrip : (Expr.stripPis (nP + 1) pty).isSome = true)
    (hI : interpExpr V cval env φ 0 (rho0 V) pty = some Pv)
    (hA : AnnotOk V cval env φ 0 (rho0 V) pty)
    (hbody : TeleBody V cval env φ (nP + 1) 0 (rho0 V) pty
      (fun _ _ xs => projV i (xs.getD nP SetTheory.empty))) :
    directProjVal V cval env pty nP i φ ∈ˢ Pv :=
  teleLamV_mem (nP + 1) hstrip hI hA hbody

/-- `⟦T.rec⟧` inhabits the interpretation of its type. -/
theorem directRecVal_mem {rty : Expr} {nP nF : Nat} {Rv : V}
    (hstrip : (Expr.stripPis (nP + 3) rty).isSome = true)
    (hI : interpExpr V cval env φ 0 (rho0 V) rty = some Rv)
    (hA : AnnotOk V cval env φ 0 (rho0 V) rty)
    (hbody : TeleBody V cval env φ (nP + 3) 0 (rho0 V) rty
      (fun _ _ xs => SpineFold V (xs.getD (nP + 1) SetTheory.empty)
        ((List.range nF).map fun j =>
          projV j (xs.getD (nP + 2) SetTheory.empty)))) :
    directRecVal V cval env rty nP nF φ ∈ˢ Rv :=
  teleLamV_mem (nP + 3) hstrip hI hA hbody

end Setlec
