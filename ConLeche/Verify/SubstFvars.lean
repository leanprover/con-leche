module

public import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Verify.InstLevels

public section

/-!
# Parallel substitution of free variables

`Expr.substFvars b D s e` replaces the free variables `0 ..< b` of `e`
by the terms `s 0, …, s (b - 1)` ALL AT ONCE and moves the others (the
binders `e`'s reading opens above `b`) to `D, D + 1, …`.  A container
frame's constructor type is the recorded member-abstracted constructor
type so substituted: the parameter variables by the
key's parameters, the member holes by the frame's holes (the reached
group) or the members' constants (the rest).  The reading side is
`denoteMeta_substFvars` (`Model/Annot/BitSubstFvars.lean`).
-/

namespace ConLeche.Expr

/-- **Parallel substitution** of the free variables below `b`; the ones
at or above `b` are moved to start at `D`. -/
@[expose] def substFvars (b D : Nat) (s : Nat → Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar i ty => if i < b then s i else .fvar (i - b + D) (substFvars b D s ty)
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (substFvars b D s f) (substFvars b D s a)
  | .lam ty body m => .lam (substFvars b D s ty) (substFvars b D s body) m
  | .forallE ty body m => .forallE (substFvars b D s ty) (substFvars b D s body) m
  | .letE ty val body =>
    .letE (substFvars b D s ty) (substFvars b D s val) (substFvars b D s body)
  | .lit l => .lit l
  | .proj n i e => .proj n i (substFvars b D s e)

variable {b D : Nat} {s : Nat → Expr}

theorem substFvars_fvar_lt {i : Nat} (hi : i < b) (ty : Expr) :
    substFvars b D s (.fvar i ty) = s i := by
  simp [substFvars, hi]

theorem substFvars_fvar_ge {i : Nat} (hi : b ≤ i) (ty : Expr) :
    substFvars b D s (.fvar i ty) = .fvar (i - b + D) (substFvars b D s ty) := by
  simp [substFvars, show ¬ i < b by omega]

/-- **Substitution commutes with instantiation**, when the substituted
terms have no loose bound variable. -/
theorem substFvars_instantiate1 (hs : ∀ i, i < b → (s i).looseBVarsBounded 0 = true)
    (v : Expr) : ∀ (e : Expr) (k : Nat),
      substFvars b D s (e.instantiate1 v k) = (substFvars b D s e).instantiate1 (substFvars b D s v) k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [instantiate1]
    by_cases h1 : i = k
    · subst h1; simp [substFvars]
    · by_cases h2 : i > k
      · simp [h1, h2, substFvars]
      · simp [h1, h2, substFvars]
  | fvar i ty ih =>
    intro k
    by_cases hi : i < b
    · rw [show (Expr.fvar i ty).instantiate1 v k = .fvar i ty from rfl, substFvars_fvar_lt hi,
        instantiate1_eq_self (looseBVarsBounded_mono (Nat.zero_le _) (hs i hi))]
    · rw [show (Expr.fvar i ty).instantiate1 v k = .fvar i ty from rfl,
        substFvars_fvar_ge (by omega)]
      rfl
  | sort u => intro k; rfl
  | const n us => intro k; rfl
  | lit l => intro k; rfl
  | app f a ihf iha => intro k; simp only [instantiate1, substFvars, ihf, iha]
  | lam ty body m iht ihb => intro k; simp only [instantiate1, substFvars, iht, ihb]
  | forallE ty body m iht ihb => intro k; simp only [instantiate1, substFvars, iht, ihb]
  | letE ty val body iht ihv ihb =>
    intro k; simp only [instantiate1, substFvars, iht, ihv, ihb]
  | proj n i e ih => intro k; simp only [instantiate1, substFvars, ih]

/-- **Substitution commutes with instantiating a Π telescope.** -/
theorem substFvars_instPisWith (hs : ∀ i, i < b → (s i).looseBVarsBounded 0 = true) :
    ∀ (as : List Expr) {e r : Expr}, ConLeche.instPisWith as e = some r →
      ConLeche.instPisWith (as.map (substFvars b D s)) (substFvars b D s e) = some (substFvars b D s r)
  | [], e, r, h => by
    simp only [ConLeche.instPisWith, Option.some.injEq] at h
    subst h; rfl
  | a :: as, e, r, h => by
    match e, h with
    | .forallE ty body m, h =>
      simp only [ConLeche.instPisWith] at h
      simp only [List.map_cons, substFvars, ConLeche.instPisWith]
      rw [← substFvars_instantiate1 hs a body 0]
      exact substFvars_instPisWith hs as h


/-! ## A container frame's constructor type IS the recorded one, substituted

The frame (`nestCtors`) builds `instPisWith ds ((e.instantiateLevelParams
lps us).replaceConsts sub)` from a stored constructor type `e`; the
record reads `instPisWith pf (nestAbstract ctx holes e)` (the canonical
parameter variables `pf`, the members at their holes `nP + m`).  When
every member occurrence of `e` is at the block's own levels (M2′: the
abstraction leaves no member constant), the first is the second at the
levels `us` with the parameter variables replaced by `ds` and each member
hole by the frame's hole (the reached group) or the member's constant
(the rest). -/

/-- Level instantiation commutes with instantiating a Π telescope at
variables. -/
theorem instPisWith_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ (as : List Expr) {e r : Expr}, (∀ a ∈ as, ∃ i ty, a = .fvar i ty) →
      ConLeche.instPisWith as e = some r →
      ConLeche.instPisWith (as.map (·.instantiateLevelParams ks us)) (e.instantiateLevelParams ks us)
        = some (r.instantiateLevelParams ks us)
  | [], e, r, _, h => by
    simp only [ConLeche.instPisWith, Option.some.injEq] at h
    subst h; rfl
  | a :: as, e, r, hv, h => by
    match e, h with
    | .forallE ty body m, h =>
      simp only [ConLeche.instPisWith] at h
      obtain ⟨i, tya, rfl⟩ := hv a List.mem_cons_self
      simp only [List.map_cons, instantiateLevelParams, ConLeche.instPisWith]
      rw [← instantiateLevelParams_instantiate1 ks us body 0]
      exact instPisWith_instantiateLevelParams ks us as (fun x hx => hv x (List.mem_cons_of_mem _ hx)) h

/-- **The member abstraction, at other levels and substituted, is the
frame's replacement** (see the section docstring), on a term without
free variables. -/
theorem substFvars_nestAbstract {ctx : ConLeche.NestCtx} {holes : List Expr}
    {us : List Level} {sub : Name → List Level → Option Expr}
    (hholes : ∀ mm, mm < ctx.names.length → ∃ ty, holes[mm]? = some (.fvar (ctx.nP + mm) ty))
    (hlv : (ctx.lps.map Level.param).map (Level.subst ctx.lps us) = us)
    (hb : ctx.nP + ctx.names.length ≤ b)
    (hmem : ∀ mm, mm < ctx.names.length →
      s (ctx.nP + mm) = ((sub (ctx.names.getD mm .anonymous) us).getD
        (.const (ctx.names.getD mm .anonymous) us)))
    (hout : ∀ n vs, ctx.names.contains n = false → sub n vs = none) :
    ∀ (e : Expr), e.hasFvar = false →
      (ConLeche.nestAbstract ctx holes e).nestOcc ctx.names 0 0 = false →
      substFvars b D s ((ConLeche.nestAbstract ctx holes e).instantiateLevelParams ctx.lps us)
        = (e.instantiateLevelParams ctx.lps us).replaceConsts sub := by
  intro e
  induction e with
  | bvar i => intro _ _; rfl
  | fvar i ty => intro h; simp [hasFvar] at h
  | sort u => intro _ _; rfl
  | lit l => intro _ _; rfl
  | const n vs =>
    intro _ hocc
    unfold ConLeche.nestAbstract at hocc ⊢
    simp only [replaceConsts] at hocc ⊢
    by_cases hv : (vs == ctx.lps.map Level.param) = true
    · have hvs : vs = ctx.lps.map Level.param := by simpa using hv
      rcases hf : ctx.names.findIdx? (· == n) with _ | mm
      · -- a member name is found by `findIdx?`, so `n` is no member
        have hn : ctx.names.contains n = false := by
          rw [List.findIdx?_eq_none_iff] at hf
          have hnm : n ∉ ctx.names := fun hmem => by simpa using hf n hmem
          simp [hnm]
        rw [if_pos hv]
        dsimp only
        rw [Option.getD_none]
        simp only [instantiateLevelParams, substFvars, replaceConsts]
        rw [hout n _ hn, Option.getD_none]
      · obtain ⟨hmm, hnm⟩ : mm < ctx.names.length ∧ (ctx.names[mm]'(by
            have := List.findIdx?_eq_some_iff_getElem.mp hf; exact this.1) == n) = true := by
          have := List.findIdx?_eq_some_iff_getElem.mp hf
          exact ⟨this.1, this.2.1⟩
        obtain ⟨ty, hty⟩ := hholes mm hmm
        rw [if_pos hv]
        simp only [hty, Option.getD_some, instantiateLevelParams]
        rw [substFvars_fvar_lt (by omega), hmem mm hmm, hvs, hlv]
        have hname : ctx.names.getD mm .anonymous = n := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmm, Option.getD_some]
          simpa using hnm
        rw [hname]
        rfl
    · rw [if_neg hv, Option.getD_none] at hocc ⊢
      have hn : ctx.names.contains n = false := by
        simpa [nestOcc] using hocc
      simp only [instantiateLevelParams, substFvars, replaceConsts]
      rw [hout n _ hn, Option.getD_none]
  | app f a ihf iha =>
    intro hf hocc
    simp only [hasFvar, Bool.or_eq_false_iff] at hf
    unfold ConLeche.nestAbstract at hocc ihf iha ⊢
    simp only [replaceConsts, nestOcc, Bool.or_eq_false_iff] at hocc ⊢
    simp only [instantiateLevelParams, substFvars, replaceConsts, ihf hf.1 hocc.1, iha hf.2 hocc.2]
  | lam ty body m iht ihb =>
    intro hf hocc
    simp only [hasFvar, Bool.or_eq_false_iff] at hf
    unfold ConLeche.nestAbstract at hocc iht ihb ⊢
    simp only [replaceConsts, nestOcc, Bool.or_eq_false_iff] at hocc ⊢
    simp only [instantiateLevelParams, substFvars, replaceConsts, iht hf.1 hocc.1, ihb hf.2 hocc.2]
  | forallE ty body m iht ihb =>
    intro hf hocc
    simp only [hasFvar, Bool.or_eq_false_iff] at hf
    unfold ConLeche.nestAbstract at hocc iht ihb ⊢
    simp only [replaceConsts, nestOcc, Bool.or_eq_false_iff] at hocc ⊢
    simp only [instantiateLevelParams, substFvars, replaceConsts, iht hf.1 hocc.1, ihb hf.2 hocc.2]
  | letE ty val body iht ihv ihb =>
    intro hf hocc
    simp only [hasFvar, Bool.or_eq_false_iff] at hf
    unfold ConLeche.nestAbstract at hocc iht ihv ihb ⊢
    simp only [replaceConsts, nestOcc, Bool.or_eq_false_iff] at hocc ⊢
    simp only [instantiateLevelParams, substFvars, replaceConsts, iht hf.1.1 hocc.1.1,
      ihv hf.1.2 hocc.1.2, ihb hf.2 hocc.2]
  | proj n i e ih =>
    intro hf hocc
    simp only [hasFvar] at hf
    unfold ConLeche.nestAbstract at hocc ih ⊢
    simp only [replaceConsts, nestOcc] at hocc ⊢
    simp only [instantiateLevelParams, substFvars, replaceConsts, ih hf hocc]

/-- **The frame's constructor type is the recorded one, substituted**:
the parameters by the key's `ds`, the member holes as `hmem` says, at
the levels `us`. -/
theorem frameCrest_eq {ctx : ConLeche.NestCtx} {holes : List Expr}
    {us : List Level} {sub : Name → List Level → Option Expr} {ds : List Expr}
    (hholes : ∀ mm, mm < ctx.names.length → ∃ ty, holes[mm]? = some (.fvar (ctx.nP + mm) ty))
    (hlv : (ctx.lps.map Level.param).map (Level.subst ctx.lps us) = us)
    (hb : ctx.nP + ctx.names.length ≤ b)
    (hmem : ∀ mm, mm < ctx.names.length →
      s (ctx.nP + mm) = ((sub (ctx.names.getD mm .anonymous) us).getD
        (.const (ctx.names.getD mm .anonymous) us)))
    (hout : ∀ n vs, ctx.names.contains n = false → sub n vs = none)
    (hpar : ∀ i, i < ctx.params.length → s i = ds.getD i default)
    (hpv : ∀ i, i < ctx.params.length → ∃ ty, ctx.params[i]? = some (.fvar i ty))
    (hdlen : ds.length = ctx.params.length) (hPb : ctx.params.length ≤ b)
    (hs : ∀ i, i < b → (s i).looseBVarsBounded 0 = true)
    {e A : Expr} (he : e.hasFvar = false)
    (hocc : (ConLeche.nestAbstract ctx holes e).nestOcc ctx.names 0 0 = false)
    (hA : ConLeche.instPisWith ctx.params (ConLeche.nestAbstract ctx holes e) = some A) :
    ConLeche.instPisWith ds ((e.instantiateLevelParams ctx.lps us).replaceConsts sub)
      = some (substFvars b D s (A.instantiateLevelParams ctx.lps us)) := by
  have hpv' : ∀ a ∈ ctx.params, ∃ i ty, a = .fvar i ty := by
    intro a ha
    obtain ⟨i, hi⟩ := List.getElem?_of_mem ha
    have hlt : i < ctx.params.length := (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨ty, hty⟩ := hpv i hlt
    rw [hi] at hty
    exact ⟨i, ty, Option.some.inj hty⟩
  have h1 := instPisWith_instantiateLevelParams ctx.lps us ctx.params hpv' hA
  have h2 := substFvars_instPisWith (b := b) (D := D) (s := s) hs _ h1
  rw [substFvars_nestAbstract hholes hlv hb hmem hout e he hocc] at h2
  have hmap : (ctx.params.map (·.instantiateLevelParams ctx.lps us)).map (substFvars b D s) = ds := by
    apply List.ext_getElem
    · simp [hdlen]
    · intro i h₁ h₂
      simp only [List.getElem_map, List.length_map] at h₁ ⊢
      obtain ⟨ty, hty⟩ := hpv i h₁
      obtain ⟨hlt', hty'⟩ := List.getElem?_eq_some_iff.mp hty
      rw [hty', instantiateLevelParams, substFvars_fvar_lt (by omega), hpar i h₁,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [hmap] at h2
  exact h2

end ConLeche.Expr
