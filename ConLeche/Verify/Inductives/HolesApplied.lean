module

public import ConLeche.Verify.Inductives.PosDeriv

public section

/-!
# Every member applied to the parameters, from official's uniform check

`Expr.holesApplied` (`Kernel/Inductives/Positivity.lean`): every member
hole occurs applied to exactly the canonical parameter variables, and no
member constant occurs.  The install runs it in two places only:

* BEFORE the positivity check, on every member-abstracted constructor at
  the canonical parameters (`nestUniform`, official's
  `check_uniform_ind_occs`), with the parameters' domains member-free;
* IN the positivity check, on a container instance's parameters
  (`nestCont`).

Everything the proofs read about it follows here:

* `nestUniform_inv`: the check at every stored constructor;
* `nestAbstract_nestOcc_zero`: the member-abstracted declared type names
  no member constant (every member occurrence was at the block's levels);
* `posD_holesApplied`, `memberCtorD_holesApplied`: a member
  constructor's walked normal form satisfies it — by induction over the
  positivity derivation: an ordinary piece and a Π domain are hole-free,
  a member hole is checked against the block's parameters, a container
  leaf's parameters are checked (`nestCont`) and its indices hole-free,
  and the constructor's result is the checked crest's.
-/

namespace ConLeche

/-! ## Syntactic lemmas -/

theorem holeParamsApp_nestOcc_zero {names : List Name} {lo hi : Nat} :
    ∀ (n : Nat) (e : Expr), e.holeParamsApp lo hi n = true → e.nestOcc names 0 0 = false
  | 0, .fvar i _, _ => by simp [Expr.nestOcc]
  | n + 1, .app f (.fvar j _), h => by
    simp only [Expr.holeParamsApp, Bool.and_eq_true] at h
    simp [Expr.nestOcc, holeParamsApp_nestOcc_zero n f h.2]
  | 0, .bvar _, h | 0, .sort _, h | 0, .const .., h | 0, .app .., h | 0, .lam .., h
  | 0, .forallE .., h | 0, .letE .., h | 0, .lit _, h | 0, .proj .., h => by
    simp [Expr.holeParamsApp] at h
  | _ + 1, .bvar _, h | _ + 1, .fvar .., h | _ + 1, .sort _, h | _ + 1, .const .., h
  | _ + 1, .lam .., h | _ + 1, .forallE .., h | _ + 1, .letE .., h | _ + 1, .lit _, h
  | _ + 1, .proj .., h => by simp [Expr.holeParamsApp] at h
  | _ + 1, .app _ (.bvar _), h | _ + 1, .app _ (.sort _), h | _ + 1, .app _ (.const ..), h
  | _ + 1, .app _ (.app ..), h | _ + 1, .app _ (.lam ..), h | _ + 1, .app _ (.forallE ..), h
  | _ + 1, .app _ (.letE ..), h | _ + 1, .app _ (.lit _), h | _ + 1, .app _ (.proj ..), h => by
    simp [Expr.holeParamsApp] at h

/-- A term every member of which is applied names no member constant. -/
theorem holesApplied_nestOcc_zero {names : List Name} {nP hi : Nat} :
    ∀ (e : Expr), e.holesApplied names nP hi = true → e.nestOcc names 0 0 = false := by
  intro e
  induction e with
  | bvar i => intro _; rfl
  | fvar i ty _ => intro _; simp [Expr.nestOcc]
  | sort u => intro _; rfl
  | const n us =>
    intro h
    simpa [Expr.holesApplied, Expr.nestOcc] using h
  | app f a ihf iha =>
    intro h
    simp only [Expr.holesApplied, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact holeParamsApp_nestOcc_zero _ _ h
    · simp [Expr.nestOcc, ihf h1, iha h2]
  | lam t b mm iht ihb =>
    intro h
    simp only [Expr.holesApplied, Bool.and_eq_true] at h
    simp [Expr.nestOcc, iht h.1, ihb h.2]
  | forallE t b mm iht ihb =>
    intro h
    simp only [Expr.holesApplied, Bool.and_eq_true] at h
    simp [Expr.nestOcc, iht h.1, ihb h.2]
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.holesApplied, Bool.and_eq_true] at h
    simp [Expr.nestOcc, iht h.1.1, ihv h.1.2, ihb h.2]
  | lit l => intro _; rfl
  | proj s i e ih =>
    intro h
    simp only [Expr.holesApplied] at h
    simp [Expr.nestOcc, ih h]

/-- A term free of members and holes has every member applied. -/
theorem holesApplied_of_nestOcc {names : List Name} {nP hi : Nat} :
    ∀ (e : Expr), e.nestOcc names nP hi = false → e.holesApplied names nP hi = true := by
  intro e
  induction e with
  | bvar i => intro _; rfl
  | fvar i ty _ =>
    intro h
    simp only [Expr.nestOcc, decide_eq_false_iff_not] at h
    simp [Expr.holesApplied, h]
  | sort u => intro _; rfl
  | const n us =>
    intro h
    simpa [Expr.holesApplied, Expr.nestOcc] using h
  | app f a ihf iha =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    simp [Expr.holesApplied, ihf h.1, iha h.2]
  | lam t b mm iht ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    simp [Expr.holesApplied, iht h.1, ihb h.2]
  | forallE t b mm iht ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    simp [Expr.holesApplied, iht h.1, ihb h.2]
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    simp [Expr.holesApplied, iht h.1.1, ihv h.1.2, ihb h.2]
  | lit l => intro _; rfl
  | proj s i e ih =>
    intro h
    simp only [Expr.nestOcc] at h
    simp [Expr.holesApplied, ih h]

/-- Instantiating a bound variable by a non-hole variable above the
parameters keeps a hole applied to exactly the parameters (and a term
that is not one, not one). -/
theorem holeParamsApp_instantiate1 {lo hi D : Nat} (hD : ¬ (lo ≤ D ∧ D < hi)) (ty : Expr) :
    ∀ (n : Nat) (e : Expr) (k : Nat), n ≤ D →
      (e.instantiate1 (.fvar D ty) k).holeParamsApp lo hi n = e.holeParamsApp lo hi n
  | 0, .bvar i, k, _ => by
    simp only [Expr.instantiate1]
    split
    · simp [Expr.holeParamsApp, hD]
    · split <;> simp [Expr.holeParamsApp]
  | n + 1, .bvar i, k, _ => by
    simp only [Expr.instantiate1]
    split
    · simp [Expr.holeParamsApp]
    · split <;> simp [Expr.holeParamsApp]
  | n + 1, .app f a, k, hn => by
    have ih := holeParamsApp_instantiate1 hD ty n f k (by omega)
    cases a with
    | bvar i =>
      simp only [Expr.instantiate1]
      split
      · simp only [Expr.holeParamsApp]
        have : (D == n) = false := by simp; omega
        simp [this]
      · split <;> simp [Expr.holeParamsApp]
    | fvar j t => simp [Expr.instantiate1, Expr.holeParamsApp, ih]
    | _ => simp [Expr.instantiate1, Expr.holeParamsApp]
  | 0, .fvar .., _, _ | 0, .sort _, _, _ | 0, .const .., _, _ | 0, .app .., _, _
  | 0, .lam .., _, _ | 0, .forallE .., _, _ | 0, .letE .., _, _ | 0, .lit _, _, _
  | 0, .proj .., _, _ => by simp [Expr.instantiate1, Expr.holeParamsApp]
  | _ + 1, .fvar .., _, _ | _ + 1, .sort _, _, _ | _ + 1, .const .., _, _
  | _ + 1, .lam .., _, _ | _ + 1, .forallE .., _, _ | _ + 1, .letE .., _, _
  | _ + 1, .lit _, _, _ | _ + 1, .proj .., _, _ => by
    simp [Expr.instantiate1, Expr.holeParamsApp]

/-- The check survives instantiating a bound variable by a variable above
the holes. -/
theorem holesApplied_instantiate1 {names : List Name} {nP hi D : Nat} (hD : hi ≤ D)
    (hP : nP ≤ D) (ty : Expr) :
    ∀ (e : Expr) (k : Nat), e.holesApplied names nP hi = true →
      (e.instantiate1 (.fvar D ty) k).holesApplied names nP hi = true := by
  have hD' : ¬ (nP ≤ D ∧ D < hi) := by omega
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · simp [Expr.holesApplied, hD']
    · split <;> rfl
  | fvar i t _ => intro k h; exact h
  | sort u => intro k h; exact h
  | const n us => intro k h; exact h
  | lit l => intro k h; exact h
  | app f a ihf iha =>
    intro k h
    simp only [Expr.holesApplied, Bool.or_eq_true, Bool.and_eq_true] at h
    have hpa := holeParamsApp_instantiate1 hD' ty nP (.app f a) k hP
    simp only [Expr.instantiate1] at hpa ⊢
    simp only [Expr.holesApplied, Bool.or_eq_true, Bool.and_eq_true, hpa]
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨ihf k h1, iha k h2⟩
  | lam t b mm iht ihb =>
    intro k h
    simp only [Expr.holesApplied, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, Expr.holesApplied, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE t b mm iht ihb =>
    intro k h
    simp only [Expr.holesApplied, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, Expr.holesApplied, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE t v b iht ihv ihb =>
    intro k h
    simp only [Expr.holesApplied, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, Expr.holesApplied, Bool.and_eq_true]
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i e ih =>
    intro k h
    simp only [Expr.holesApplied] at h
    simp only [Expr.instantiate1, Expr.holesApplied]
    exact ih k h

/-- Abstracting a non-hole variable above the parameters keeps a hole
applied to exactly the parameters (and a term that is not one, not one). -/
theorem holeParamsApp_abstract1 {lo hi D : Nat} (hD : ¬ (lo ≤ D ∧ D < hi)) :
    ∀ (n : Nat) (e : Expr) (k : Nat), n ≤ D →
      (e.abstract1 D k).holeParamsApp lo hi n = e.holeParamsApp lo hi n
  | 0, .fvar i t, k, _ => by
    simp only [Expr.abstract1]
    split
    · rename_i h; subst h; simp [Expr.holeParamsApp, hD]
    · rfl
  | n + 1, .fvar i t, k, _ => by
    simp only [Expr.abstract1]
    split <;> simp [Expr.holeParamsApp]
  | n + 1, .app f a, k, hn => by
    have ih := holeParamsApp_abstract1 hD n f k (by omega)
    cases a with
    | fvar j t =>
      simp only [Expr.abstract1]
      split
      · rename_i h; subst h
        simp only [Expr.holeParamsApp]
        have : (j == n) = false := by simp; omega
        simp [this]
      · simp [Expr.holeParamsApp, ih]
    | _ => simp [Expr.abstract1, Expr.holeParamsApp]
  | 0, .bvar _, _, _ | 0, .sort _, _, _ | 0, .const .., _, _ | 0, .app .., _, _
  | 0, .lam .., _, _ | 0, .forallE .., _, _ | 0, .letE .., _, _ | 0, .lit _, _, _
  | 0, .proj .., _, _ => by simp [Expr.abstract1, Expr.holeParamsApp]
  | _ + 1, .bvar _, _, _ | _ + 1, .sort _, _, _ | _ + 1, .const .., _, _
  | _ + 1, .lam .., _, _ | _ + 1, .forallE .., _, _ | _ + 1, .letE .., _, _
  | _ + 1, .lit _, _, _ | _ + 1, .proj .., _, _ => by
    simp [Expr.abstract1, Expr.holeParamsApp]

/-- The check survives abstracting a variable above the holes. -/
theorem holesApplied_abstract1 {names : List Name} {nP hi D : Nat} (hD : hi ≤ D)
    (hP : nP ≤ D) :
    ∀ (e : Expr) (k : Nat), e.holesApplied names nP hi = true →
      (e.abstract1 D k).holesApplied names nP hi = true := by
  have hD' : ¬ (nP ≤ D ∧ D < hi) := by omega
  intro e
  induction e with
  | fvar i t _ =>
    intro k h
    simp only [Expr.abstract1]
    split
    · rfl
    · exact h
  | bvar i => intro k h; exact h
  | sort u => intro k h; exact h
  | const n us => intro k h; exact h
  | lit l => intro k h; exact h
  | app f a ihf iha =>
    intro k h
    simp only [Expr.holesApplied, Bool.or_eq_true, Bool.and_eq_true] at h
    have hpa := holeParamsApp_abstract1 hD' nP (.app f a) k hP
    simp only [Expr.abstract1] at hpa ⊢
    simp only [Expr.holesApplied, Bool.or_eq_true, Bool.and_eq_true, hpa]
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨ihf k h1, iha k h2⟩
  | lam t b mm iht ihb =>
    intro k h
    simp only [Expr.holesApplied, Bool.and_eq_true] at h
    simp only [Expr.abstract1, Expr.holesApplied, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE t b mm iht ihb =>
    intro k h
    simp only [Expr.holesApplied, Bool.and_eq_true] at h
    simp only [Expr.abstract1, Expr.holesApplied, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE t v b iht ihv ihb =>
    intro k h
    simp only [Expr.holesApplied, Bool.and_eq_true] at h
    simp only [Expr.abstract1, Expr.holesApplied, Bool.and_eq_true]
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i e ih =>
    intro k h
    simp only [Expr.holesApplied] at h
    simp only [Expr.abstract1, Expr.holesApplied]
    exact ih k h

/-- A closed-over telescope keeps the check (its variables above the holes). -/
theorem holesApplied_closeTelescope {names : List Name} {nP hi : Nat} :
    ∀ (nds : List (Expr × BinderMeta)) (i : Nat) (body : Expr), hi ≤ i → nP ≤ i →
      (∀ p ∈ nds, p.1.holesApplied names nP hi = true) →
      body.holesApplied names nP hi = true →
      (closeTelescope nds i body).holesApplied names nP hi = true
  | [], _, _, _, _, _, hb => hb
  | (dom, bm) :: bs, i, body, hi', hP, hn, hb => by
    simp only [closeTelescope, Expr.holesApplied, Bool.and_eq_true]
    refine ⟨hn _ List.mem_cons_self, holesApplied_abstract1 hi' hP _ 0 ?_⟩
    exact holesApplied_closeTelescope bs (i + 1) body (by omega) (by omega)
      (fun p hp => hn p (List.mem_cons_of_mem _ hp)) hb

/-- A spine whose head and arguments pass passes. -/
theorem holesApplied_spine {names : List Name} {nP hi : Nat} :
    ∀ (w : Expr), w.getAppFn.holesApplied names nP hi = true →
      (∀ a ∈ w.getAppArgs, a.holesApplied names nP hi = true) →
      w.holesApplied names nP hi = true := by
  intro w
  induction w with
  | app f a ihf _ =>
    intro hf ha
    simp only [Expr.getAppFn] at hf
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at ha
    simp only [Expr.holesApplied, Bool.or_eq_true, Bool.and_eq_true]
    exact Or.inr ⟨ihf hf fun x hx => ha x (Or.inl hx), ha a (Or.inr rfl)⟩
  | _ => intro hf _; simpa [Expr.getAppFn] using hf

/-- A hole's spine at exactly `n` positional parameter variables. -/
theorem holeParamsApp_spine {lo hi i : Nat} {ty : Expr} (hi1 : lo ≤ i) (hi2 : i < hi) :
    ∀ (w : Expr) (n : Nat), w.getAppFn = .fvar i ty → w.getAppArgs.length = n →
      (∀ (j : Nat) (x : Expr), w.getAppArgs[j]? = some x → ∃ t, x = .fvar j t) →
      w.holeParamsApp lo hi n = true := by
  intro w
  induction w with
  | app f a ihf _ =>
    intro n hfn hlen hpos
    simp only [Expr.getAppFn] at hfn
    simp only [Expr.getAppArgs, List.length_append, List.length_singleton] at hlen
    obtain ⟨t, rfl⟩ := hpos f.getAppArgs.length a (by simp [Expr.getAppArgs])
    obtain rfl : n = f.getAppArgs.length + 1 := hlen.symm
    simp only [Expr.holeParamsApp, beq_self_eq_true, Bool.true_and]
    exact ihf _ hfn rfl fun j x hx => hpos j x (by
      simp only [Expr.getAppArgs]; rw [List.getElem?_append_left
        (List.getElem?_eq_some_iff.mp hx).1]; exact hx)
  | fvar k t =>
    intro n hfn hlen _
    simp only [Expr.getAppFn, Expr.fvar.injEq] at hfn
    obtain ⟨rfl, -⟩ := hfn
    simp only [Expr.getAppArgs, List.length_nil] at hlen
    subst hlen
    simp [Expr.holeParamsApp, hi1, hi2]
  | _ => intro n hfn; simp [Expr.getAppFn] at hfn

/-- A member hole applied to the positional parameter variables, then to
arguments that pass, passes. -/
theorem holesApplied_holeSpine {names : List Name} {nP hi i : Nat} {ty : Expr}
    (hi1 : nP ≤ i) (hi2 : i < hi) {params : List Expr} (hplen : params.length = nP)
    (hpos : ∀ (j : Nat) (x : Expr), params[j]? = some x → ∃ t, x = .fvar j t) :
    ∀ (w : Expr), w.getAppFn = .fvar i ty → nP ≤ w.getAppArgs.length →
      w.getAppArgs.take nP = params →
      (∀ a ∈ w.getAppArgs.drop nP, a.holesApplied names nP hi = true) →
      w.holesApplied names nP hi = true := by
  intro w
  induction w with
  | app f a ihf _ =>
    intro hfn hlen htake hdrop
    simp only [Expr.getAppFn] at hfn
    simp only [Expr.getAppArgs, List.length_append, List.length_singleton] at hlen htake hdrop
    by_cases hn : f.getAppArgs.length + 1 = nP
    · -- exactly the parameters: the whole spine is the hole applied
      simp only [Expr.holesApplied, Bool.or_eq_true]
      refine Or.inl (holeParamsApp_spine hi1 hi2 (.app f a) nP hfn
        (by simp [Expr.getAppArgs]; omega) fun j x hx => hpos j x ?_)
      rw [← htake, List.getElem?_take]
      simp only [Expr.getAppArgs] at hx
      have := (List.getElem?_eq_some_iff.mp hx).1
      simp only [List.length_append, List.length_singleton] at this
      rw [if_pos (by omega)]
      exact hx
    · have hle : nP ≤ f.getAppArgs.length := by omega
      simp only [Expr.holesApplied, Bool.or_eq_true, Bool.and_eq_true]
      refine Or.inr ⟨ihf hfn hle ?_ fun x hx => hdrop x ?_, hdrop a ?_⟩
      · rw [← htake, List.take_append_of_le_length hle]
      · rw [List.drop_append_of_le_length hle]; exact List.mem_append_left _ hx
      · rw [List.drop_append_of_le_length hle]; exact List.mem_append_right _ List.mem_cons_self
  | fvar k t =>
    intro hfn hlen _ _
    simp only [Expr.getAppFn, Expr.fvar.injEq] at hfn
    obtain ⟨rfl, -⟩ := hfn
    simp only [Expr.getAppArgs, List.length_nil, Nat.le_zero] at hlen
    subst hlen
    simp [Expr.holesApplied, Expr.holeParamsApp, hi1, hi2]
  | _ => intro hfn; simp [Expr.getAppFn] at hfn

/-! ## The derivation's normal forms -/

section Deriv

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}

/-- **Every root normal form has every member applied**: by induction on
the positivity derivation, at no frames (the root's walk).  A field's
normal form: hole-free (`const`, a Π's domain), a member hole checked
against the parameters (`hole`), a container leaf whose parameters the
walk checked (`nestCont`) and whose indices are hole-free; a telescope's
fields, and its result when its input passes (the opening variables lie
above the holes). -/
theorem posD_holesApplied (hplen : ctx.params.length = ctx.nP)
    (hpos : ∀ (j : Nat) (x : Expr), ctx.params[j]? = some x → ∃ t, x = .fvar j t) :
    ∀ {J : PosJ} {ts : List PosTree}, PosD ops env ctx J ts → match J with
      | .field prog dep _ _ _ nf => prog = [] → ctx.hiAt 0 ≤ dep →
          nf.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true
      | .tele prog base _ _ cur _ nds res => prog = [] → ctx.hiAt 0 ≤ base →
          (∀ p ∈ nds, p.1.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true) ∧
          (cur.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true →
            res.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true)
      | _ => True := by
  have hPhi : ctx.nP ≤ ctx.hiAt 0 := by simp [NestCtx.hiAt]
  intro J ts h
  induction h with
  | @const prog dep kb e w hw hocc =>
    intro hp _
    subst hp
    split
    · exact holesApplied_of_nestOcc _ hocc
    · rename_i hn; exact holesApplied_of_nestOcc _ (by simpa using hn)
  | @pi prog dep kb e a b bm k nb ts hw hocc ha hb ihb =>
    intro hp hd
    subst hp
    simp only [Expr.holesApplied, Bool.and_eq_true]
    exact ⟨holesApplied_of_nestOcc _ ha,
      holesApplied_abstract1 hd (by omega) nb 0 (ihb rfl (by omega))⟩
  | @hole prog dep kb e w i ty hw hocc hfn hlo hhi hlen hpar hfree =>
    intro hp _
    subst hp
    refine holesApplied_holeSpine hlo hhi hplen hpos w hfn (by omega) hpar fun a ha => ?_
    exact holesApplied_of_nestOcc _ (hfree a (List.mem_of_mem_drop ha))
  | @frameHole prog dep kb e w i ty h hw hocc hfn hlo hhi' =>
    intro hp _
    subst hp
    simp only [List.length_nil] at hhi'
    omega
  | @contNew prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hq hlen hquot hidx hds hdsw
      hdsA =>
    intro hp _
    subst hp
    refine holesApplied_spine w (by simpa [hfn, Expr.holesApplied] using hnm) fun a ha => ?_
    rw [← List.take_append_drop nPc w.getAppArgs, List.mem_append] at ha
    rcases ha with ha | ha
    · exact hdsA a ha
    · exact holesApplied_of_nestOcc _ (hidx a ha)
  | @contHit prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hq hlen hquot hidx hds hdsw
      hdsA =>
    intro hp _
    subst hp
    refine holesApplied_spine w (by simpa [hfn, Expr.holesApplied] using hnm) fun a ha => ?_
    rw [← List.take_append_drop nPc w.getAppArgs, List.mem_append] at ha
    rcases ha with ha | ha
    · exact hdsA a ha
    · exact holesApplied_of_nestOcc _ (hidx a ha)
  | teleNil => intro _ _; exact ⟨fun _ h => (nomatch h), id⟩
  | @teleCons prog base nF j a b bm k nd ks nds res ts ts' ha hb iha ihb =>
    intro hp hbase
    obtain ⟨h1, h2⟩ := ihb hp hbase
    have hnd := iha hp (by omega)
    refine ⟨fun p hp' => ?_, fun hcur => h2 ?_⟩
    · rcases List.mem_cons.mp hp' with rfl | hp'
      · exact hnd
      · exact h1 p hp'
    · simp only [Expr.holesApplied, Bool.and_eq_true] at hcur
      exact holesApplied_instantiate1 (by omega) (by omega) a b 0 hcur.2
  | _ => trivial

/-- **A member constructor's normal form has every member applied**, when
its crest does (`nestUniform`). -/
theorem memberCtorD_holesApplied (hplen : ctx.params.length = ctx.nP)
    (hpos : ∀ (j : Nat) (x : Expr), ctx.params[j]? = some x → ∃ t, x = .fvar j t)
    {nF : Nat} {crest : Expr} {ks : List NestFieldKind} {nds : List (Expr × BinderMeta)}
    {cur : Expr} {ts : List PosTree}
    (htele : PosD ops env ctx (.tele [] (ctx.hiAt 0) nF 0 crest ks nds cur) ts)
    (hcrest : crest.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true) :
    (closeTelescope nds (ctx.hiAt 0) cur).holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true := by
  obtain ⟨h1, h2⟩ := posD_holesApplied hplen hpos htele rfl (Nat.le_refl _)
  exact holesApplied_closeTelescope nds _ cur (Nat.le_refl _) (by simp [NestCtx.hiAt]) h1
    (h2 hcrest)

end Deriv

/-! ## The uniform check, inverted -/

/-- `nestUniform` passed: the check at every stored constructor. -/
theorem nestUniform_inv {ctx : NestCtx} {holes : List Expr}
    {ctorss : List (List (ConstantVal × Nat))}
    (h : nestUniform (m := CheckM) ctx holes ctorss = .ok ()) :
    ∀ cs ∈ ctorss, ∀ c ∈ cs, nestUniformOk ctx holes c.1.type = true := by
  unfold nestUniform at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rename_i hn
    intro cs hcs c hc
    rw [List.findSome?_eq_none_iff] at hn
    have := List.find?_eq_none.mp (hn cs hcs) c hc
    simpa using this

/-- Instantiating a bound variable by a free one changes no member constant. -/
theorem nestOcc_zero_instantiate1 {names : List Name} {i : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), (e.instantiate1 (.fvar i ty) k).nestOcc names 0 0 =
      e.nestOcc names 0 0 := by
  intro e
  induction e with
  | bvar j =>
    intro k
    simp only [Expr.instantiate1]
    split
    · simp [Expr.nestOcc]
    · split <;> rfl
  | app f a ihf iha => intro k; simp [Expr.instantiate1, Expr.nestOcc, ihf, iha]
  | lam t b mm iht ihb => intro k; simp [Expr.instantiate1, Expr.nestOcc, iht, ihb]
  | forallE t b mm iht ihb => intro k; simp [Expr.instantiate1, Expr.nestOcc, iht, ihb]
  | letE t v b iht ihv ihb => intro k; simp [Expr.instantiate1, Expr.nestOcc, iht, ihv, ihb]
  | proj s j e ih => intro k; simp [Expr.instantiate1, Expr.nestOcc, ih]
  | _ => intro k; rfl

/-- No member or hole is in particular no member constant. -/
theorem nestOcc_zero_of {names : List Name} {lo hi : Nat} :
    ∀ (e : Expr), e.nestOcc names lo hi = false → e.nestOcc names 0 0 = false := by
  intro e
  induction e with
  | fvar i ty _ => intro _; simp [Expr.nestOcc]
  | app f a ihf iha =>
    intro h; simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h ⊢; exact ⟨ihf h.1, iha h.2⟩
  | lam t b mm iht ihb =>
    intro h; simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h ⊢; exact ⟨iht h.1, ihb h.2⟩
  | forallE t b mm iht ihb =>
    intro h; simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h ⊢; exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h; simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s j e ih => intro h; simp only [Expr.nestOcc] at h ⊢; exact ih h
  | _ => intro h; exact h

/-- No member or hole in the parameters' domains is in particular no member
constant there. -/
theorem piDomsOcc_zero_of {names : List Name} {lo hi : Nat} :
    ∀ (n : Nat) (e : Expr), e.piDomsOcc names lo hi n = false → e.piDomsOcc names 0 0 n = false
  | 0, _, _ => rfl
  | n + 1, .forallE d b bm, h => by
    simp only [Expr.piDomsOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨nestOcc_zero_of _ h.1, piDomsOcc_zero_of n b h.2⟩
  | _ + 1, .bvar _, _ | _ + 1, .fvar .., _ | _ + 1, .sort _, _ | _ + 1, .const .., _
  | _ + 1, .app .., _ | _ + 1, .lam .., _ | _ + 1, .letE .., _ | _ + 1, .lit _, _
  | _ + 1, .proj .., _ => rfl

/-- The parameters' domains name the same member constants after
instantiating a bound variable by a free one. -/
theorem piDomsOcc_zero_instantiate1 {names : List Name} {x : Nat} {t : Expr} :
    ∀ (n : Nat) (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar x t) k).piDomsOcc names 0 0 n = e.piDomsOcc names 0 0 n
  | 0, _, _ => rfl
  | n + 1, .forallE d b bm, k => by
    simp only [Expr.instantiate1, Expr.piDomsOcc, nestOcc_zero_instantiate1,
      piDomsOcc_zero_instantiate1 n b (k + 1)]
  | _ + 1, .bvar j, k => by
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | _ + 1, .fvar .., _ | _ + 1, .sort _, _ | _ + 1, .const .., _
  | _ + 1, .app .., _ | _ + 1, .lam .., _ | _ + 1, .letE .., _ | _ + 1, .lit _, _
  | _ + 1, .proj .., _ => rfl

/-- A telescope whose parameters' domains name no member constant and
whose body at the (free-variable) parameters names none names none. -/
theorem nestOcc_zero_of_instPisWith {names : List Name} :
    ∀ (ps : List Expr) (e crest : Expr), (∀ p ∈ ps, ∃ i ty, p = .fvar i ty) →
      instPisWith ps e = some crest → e.piDomsOcc names 0 0 ps.length = false →
      crest.nestOcc names 0 0 = false → e.nestOcc names 0 0 = false
  | [], e, crest, _, hi', _, hc => by
    simp only [instPisWith, Option.some.injEq] at hi'
    subst hi'; exact hc
  | p :: ps, .forallE d b bm, crest, hp, hi', hd, hc => by
    obtain ⟨i, ty, rfl⟩ := hp _ List.mem_cons_self
    simp only [instPisWith] at hi'
    simp only [List.length_cons, Expr.piDomsOcc, Bool.or_eq_false_iff] at hd
    have hb := nestOcc_zero_of_instPisWith ps _ crest
      (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hi'
      (by rw [piDomsOcc_zero_instantiate1]; exact hd.2) hc
    rw [nestOcc_zero_instantiate1] at hb
    simp [Expr.nestOcc, hd.1, hb]
  | _ :: _, .bvar _, _, _, h, _, _ | _ :: _, .fvar .., _, _, h, _, _
  | _ :: _, .sort _, _, _, h, _, _ | _ :: _, .const .., _, _, h, _, _
  | _ :: _, .app .., _, _, h, _, _ | _ :: _, .lam .., _, _, h, _, _
  | _ :: _, .letE .., _, _, h, _, _ | _ :: _, .lit _, _, _, h, _, _
  | _ :: _, .proj .., _, _, h, _, _ => by simp [instPisWith] at h

/-- **M2′ from the uniform check**: a constructor type that passed
`nestUniformOk` and instantiates at the canonical parameters has a member
abstraction naming no member constant — every member occurrence was at
the block's own levels. -/
theorem nestAbstract_nestOcc_zero {ctx : NestCtx} {holes : List Expr} {ty : Expr}
    (hpar : ∀ p ∈ ctx.params, ∃ i t, p = .fvar i t) (hplen : ctx.params.length = ctx.nP)
    (hu : nestUniformOk ctx holes ty = true) :
    (nestAbstract ctx holes ty).nestOcc ctx.names 0 0 = false := by
  simp only [nestUniformOk, Bool.and_eq_true, Bool.not_eq_true'] at hu
  obtain ⟨hd, hb⟩ := hu
  split at hb
  case h_2 => exact nomatch hb
  rename_i crest hcr
  refine nestOcc_zero_of_instPisWith ctx.params _ crest hpar hcr ?_
    (holesApplied_nestOcc_zero _ hb)
  rw [hplen]; exact piDomsOcc_zero_of _ _ hd

/-- The crest of a constructor that passed `nestUniformOk` has every
member applied. -/
theorem crest_holesApplied {ctx : NestCtx} {holes : List Expr} {ty crest : Expr}
    (hu : nestUniformOk ctx holes ty = true)
    (hcr : instPisWith ctx.params (nestAbstract ctx holes ty) = some crest) :
    crest.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true := by
  simp only [nestUniformOk, Bool.and_eq_true, hcr] at hu
  exact hu.2

end ConLeche
