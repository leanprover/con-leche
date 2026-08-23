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

/-- The constructor's field telescope, instantiated at the **type
former's** opened parameter variables (junk outside the class).  The
type former's opening is the block's one frame: `checkDirectCtor` runs
the per-field universe walk over exactly this residual, so the field
types' annotations are the ones the type former's own telescope walk
supplies. -/
def directCRest (tty cty : Expr) (nP : Nat) : Expr :=
  match openPisAtFvars nP tty 0 with
  | some (fvsP, _) =>
    match Expr.instPisAt fvsP cty with
    | some (_, crest) => crest
    | none => .sort .zero
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
      (directCRest tty cty nP))

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
    (hfield : ∀ (ps' : List V) (d : Nat) (ρ : Nat → V),
      TeleFit V cval env φ 0 (rho0 V) tty ps' d ρ (.sort s) →
      ps'.length = nP →
      FieldTele V cval env φ (s.eval φ) nF d ρ (directCRest tty cty nP)) :
    SpineFold V (directTyVal V cval env tty cty nP nF s φ) ps =
      sigmaTowerV V cval env φ (s.eval φ) nF d' ρ' (directCRest tty cty nP) := by
  rw [directTyVal, teleLamV_fold (S := fun d ρ _ =>
      directTyBody V cval env φ (s.eval φ) nF d ρ (directCRest tty cty nP))
    (by rw [hstrip]; rfl) hfit hlen htyA
    (fun xs d₂ ρ₂ rest hfit₂ hlen₂ =>
      ⟨univ (s.eval φ), by rw [TeleFit_rest_sort nP hfit₂ hlen₂ hstrip,
        interpExpr], directTyBody_mem_univ⟩)]
  exact directTyBody_eq (hfield ps d' ρ' hfit hlen)

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
    (fun _ _ _ _ _ => trivial)
  rw [hfold] at hx hy
  rw [mem_unitSet_iff.mp hx, mem_unitSet_iff.mp hy]

/-! ### The constructor's value -/

/-- `⟦T.mk⟧`: the λ-tower over the constructor's telescope whose body is
the tuple of the *field* values. -/
noncomputable def directCtorVal (V : Type u) [SetTheory V] (cval : ConstVal V)
    (env : Env) (cty : Expr) (nP nF : Nat) (ψ : Name → Nat) : V :=
  teleLamV V cval env ψ (nP + nF) 0 (rho0 V) cty
    (fun _ _ xs => tupleV (xs.drop nP))

/-- The constructor's value inhabits the interpretation of its type.
The two hypotheses are what the install establishes: the field
telescope is a `FieldTele` at every parameter instantiation (the
universe bound), and the constructor's residual — the type former
applied to exactly the parameters — interprets to the very tower that
`⟦T⟧` unfolds to at those parameters. -/
theorem directCtorVal_mem {cty : Expr} {nP nF w : Nat} {Cv : V}
    (hw : w ≠ 0)
    (hstrip : (Expr.stripPis (nP + nF) cty).isSome = true)
    (hctyI : interpExpr V cval env φ 0 (rho0 V) cty = some Cv)
    (hctyA : AnnotOk V cval env φ 0 (rho0 V) cty)
    (hfield : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (mid : Expr),
      TeleFit V cval env φ 0 (rho0 V) cty ps d₁ ρ₁ mid → ps.length = nP →
      FieldTele V cval env φ w nF d₁ ρ₁ mid)
    (hresid : ∀ (ps fs : List V) (d₁ : Nat) (ρ₁ : Nat → V) (mid : Expr)
      (d' : Nat) (ρ' : Nat → V) (rest : Expr),
      TeleFit V cval env φ 0 (rho0 V) cty ps d₁ ρ₁ mid → ps.length = nP →
      TeleFit V cval env φ d₁ ρ₁ mid fs d' ρ' rest → fs.length = nF →
      interpExpr V cval env φ d' ρ' rest =
        some (sigmaTowerV V cval env φ w nF d₁ ρ₁ mid)) :
    directCtorVal V cval env cty nP nF φ ∈ˢ Cv := by
  refine teleLamV_mem (nP + nF) hstrip hctyI hctyA ?_
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
projection type (`directProjTy`) spells. -/
theorem directProj_body_mem {w nF d₁ : Nat} {ρ₁ : Nat → V} {mid : Expr}
    {x : V} {i : Nat} {Q : V}
    (hw : w ≠ 0) (hi : i < nF)
    (hfld : FieldTele V cval env φ w nF d₁ ρ₁ mid)
    (hx : x ∈ˢ sigmaTowerV V cval env φ w nF d₁ ρ₁ mid)
    (hdom : ∀ (fs : List V) (d' : Nat) (ρ' : Nat → V) (rest : Expr),
      TeleFit V cval env φ d₁ ρ₁ mid fs d' ρ' rest → fs.length = nF →
      fs.getD i SetTheory.empty ∈ˢ Q) :
    projV i x ∈ˢ Q := by
  obtain ⟨d', ρ', rest, hfit, -⟩ := sigmaTowerV_split hw hfld hx
  have h := hdom _ d' ρ' rest hfit (by simp)
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
