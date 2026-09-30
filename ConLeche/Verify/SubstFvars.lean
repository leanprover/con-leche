module

public import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Verify.InstLevels
public import ConLeche.Verify.Inductives.ReplaceApps

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

The frame (`nestCtors`) builds `nestCrest names us ds holes (e.instantiateLevelParams
lps us)` from a stored constructor type `e`: its canonical abstraction at
the frame's levels (the group's whole applications to the canonical holes,
`nestCanonCrest`), the canonical variables then replaced by the key's
parameters and the frame's holes.  The record reads the canonical
abstraction at the block's own levels (`nestCanonCrest names' (lps.map
param) n e`).  When that abstraction leaves no member constant (official's
uniform check at the container's install), the first is the second at
the levels `us` with the canonical parameter variables replaced by `ds`
and each canonical hole by the frame's hole of the same member — the
frame's group may list the members in another order. -/

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

theorem nestPhs_instantiateLevelParams (ks : List Name) (us : List Level) (n : Nat) :
    (ConLeche.nestPhs n).map (·.instantiateLevelParams ks us) = ConLeche.nestPhs n := by
  simp [ConLeche.nestPhs, instantiateLevelParams, Level.subst]

/-! ### The placeholder spine -/

theorem phApp?_zero {b : Nat} {e : Expr} {p : Name × List Level} (h : e.phApp? b 0 = some p) :
    e = .const p.1 p.2 := by
  obtain ⟨c, v⟩ := p
  cases e <;> simp_all [phApp?]

theorem phApp?_succ {b k : Nat} {e : Expr} {p : Name × List Level}
    (h : e.phApp? b (k + 1) = some p) :
    ∃ f ty, e = .app f (.fvar (b + k) ty) ∧ f.phApp? b k = some p := by
  match e, h with
  | .app f (.fvar j ty), h =>
    simp only [phApp?] at h
    split at h
    · rename_i hj; subst hj; exact ⟨f, ty, rfl, h⟩
    · exact nomatch h

/-- A placeholder spine is not one of more arguments. -/
theorem phApp?_short {b : Nat} :
    ∀ (k : Nat) {e : Expr} {p : Name × List Level}, e.phApp? b k = some p →
      ∀ m, k < m → e.phApp? b m = none
  | 0, e, p, h, m, hm => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [phApp?_zero h]; rfl
  | k + 1, e, p, h, m, hm => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨f, ty, rfl, -⟩ := phApp?_succ h
    simp only [phApp?]
    rw [if_neg (by omega)]

/-- **An unreplaced placeholder spine keeps its head**: a spine whose head
is a member constant, left unreplaced at the top, leaves that constant in
the result. -/
theorem nestOcc_replaceApps_head {f : Name → List Level → Option Expr} {b n : Nat}
    {names : List Name} {lo hi : Nat} {c : Name} {v : List Level} (hc : names.contains c = true) :
    ∀ (k : Nat) (e : Expr), e.phApp? b k = some (c, v) → k ≤ n →
      (k < n ∨ e.appHole? f b n = none) → (e.replaceApps f b n).nestOcc names lo hi = true
  | 0, e, h, _, hno => by
    have he := phApp?_zero h
    simp only at he
    subst he
    have hnone : (Expr.const c v).appHole? f b n = none := by
      rcases hno with hlt | hno
      · simp [appHole?, phApp?_short 0 h n hlt]
      · exact hno
    rw [replaceApps_const, hnone]
    simpa [nestOcc] using hc
  | k + 1, e, h, hk, hno => by
    obtain ⟨f', ty, rfl, h'⟩ := phApp?_succ h
    have hnone : (Expr.app f' (.fvar (b + k) ty)).appHole? f b n = none := by
      rcases hno with hlt | hno
      · simp [appHole?, phApp?_short (k + 1) h n hlt]
      · exact hno
    rw [replaceApps_app, hnone]
    simp only [nestOcc, Bool.or_eq_true]
    exact .inl (nestOcc_replaceApps_head hc k f' h' (by omega) (.inl (by omega)))

/-- Level instantiation moves through the placeholder spine. -/
theorem phApp?_instantiateLevelParams (ks : List Name) (us : List Level) {b : Nat} :
    ∀ (n : Nat) (e : Expr), (e.instantiateLevelParams ks us).phApp? b n
      = (e.phApp? b n).map fun p => (p.1, p.2.map (Level.subst ks us))
  | 0, e => by cases e <;> simp [phApp?, instantiateLevelParams]
  | n + 1, e => by
    cases e with
    | app f x =>
      cases x with
      | fvar j ty =>
        simp only [instantiateLevelParams, phApp?]
        split
        · exact phApp?_instantiateLevelParams ks us n f
        · rfl
      | _ => rfl
    | _ => rfl

end ConLeche.Expr

namespace ConLeche.Expr

/-! ### The canonical abstraction at other levels, at another group order -/

/-- The canonical substitution by its hits: a member of the group at the
levels. -/
theorem nestCanonSub_eq {names : List Name} {us : List Level} {n : Nat} {c : Name}
    {v : List Level} :
    ConLeche.nestCanonSub names us n c v =
      if v = us ∧ c ∈ names then some (.fvar (n + names.idxOf c) (.sort .zero)) else none := by
  unfold ConLeche.nestCanonSub
  by_cases hv : v = us
  · subst hv
    simp only [beq_self_eq_true, if_true, true_and]
    by_cases hc : c ∈ names
    · rw [if_pos hc, List.findIdx?_eq_some_iff_findIdx_eq.mpr
        ⟨List.idxOf_lt_length_of_mem hc, rfl⟩]
      rfl
    · rw [if_neg hc, List.findIdx?_eq_none_iff.mpr (fun x hx => by
        cases hxc : x == c
        · rfl
        · exact absurd (eq_of_beq hxc ▸ hx) hc)]
      rfl
  · simp [hv]

theorem fvarsBelow_instantiateLevelParams' (ks : List Name) (us : List Level) {d : Nat} :
    ∀ {e : Expr}, fvarsBelow d e → fvarsBelow d (e.instantiateLevelParams ks us) := by
  intro e
  induction e <;> intro h <;> simp_all [fvarsBelow, instantiateLevelParams]

/-- **The canonical abstraction commutes with level instantiation**, when
it leaves no member constant: a member applied at the block's levels is
abstracted on both sides, and one at other levels would be left. -/
theorem replaceApps_canon_instantiateLevelParams {names lps : List Name} {us : List Level}
    {n : Nat} (hlv : (lps.map Level.param).map (Level.subst lps us) = us) :
    ∀ t : Expr,
      (t.replaceApps (ConLeche.nestCanonSub names (lps.map .param) n) 0 n).nestOcc names 0 0
        = false →
      (t.instantiateLevelParams lps us).replaceApps (ConLeche.nestCanonSub names us n) 0 n
        = (t.replaceApps (ConLeche.nestCanonSub names (lps.map .param) n) 0 n).instantiateLevelParams
            lps us := by
  -- a node's hit, both sides
  have hnode : ∀ e : Expr,
      (e.replaceApps (ConLeche.nestCanonSub names (lps.map .param) n) 0 n).nestOcc names 0 0
        = false →
      (∀ h, e.appHole? (ConLeche.nestCanonSub names (lps.map .param) n) 0 n = some h →
        (e.instantiateLevelParams lps us).appHole? (ConLeche.nestCanonSub names us n) 0 n
          = some h ∧ h.instantiateLevelParams lps us = h) ∧
      (e.appHole? (ConLeche.nestCanonSub names (lps.map .param) n) 0 n = none →
        (e.instantiateLevelParams lps us).appHole? (ConLeche.nestCanonSub names us n) 0 n
          = none) := by
    intro e hocc
    unfold appHole?
    rw [phApp?_instantiateLevelParams]
    cases hp : e.phApp? 0 n with
    | none => simp
    | some p =>
      obtain ⟨c, v⟩ := p
      simp only [Option.map_some, Option.bind_some, nestCanonSub_eq]
      by_cases hc : c ∈ names
      · by_cases hv : v = lps.map .param
        · subst hv
          simp only [hlv, hc, and_self, if_true, Option.some.injEq]
          refine ⟨fun h hh => ⟨hh ▸ rfl, by subst hh; rfl⟩, fun h => nomatch h⟩
        · -- a member at other levels is left: impossible
          exfalso
          have := nestOcc_replaceApps_head (f := ConLeche.nestCanonSub names (lps.map .param) n)
            (lo := 0) (hi := 0) (List.contains_iff_mem.mpr hc) n e hp (Nat.le_refl _)
            (.inr (by simp [appHole?, hp, nestCanonSub_eq, hv]))
          rw [hocc] at this
          exact nomatch this
      · simp [hc]
  intro t
  induction t with
  | const c v =>
    intro hocc
    obtain ⟨h1, h2⟩ := hnode _ hocc
    rw [replaceApps_const] at hocc ⊢
    simp only [instantiateLevelParams] at h1 h2 ⊢
    rw [replaceApps_const]
    cases hh : (Expr.const c v).appHole? (ConLeche.nestCanonSub names (lps.map .param) n) 0 n with
    | some h =>
      obtain ⟨h3, h4⟩ := h1 h hh
      rw [h3]; exact h4.symm
    | none =>
      rw [h2 hh]; rfl
  | app a x iha ihx =>
    intro hocc
    obtain ⟨h1, h2⟩ := hnode _ hocc
    rw [replaceApps_app] at hocc ⊢
    simp only [instantiateLevelParams] at h1 h2 ⊢
    rw [replaceApps_app]
    cases hh : (Expr.app a x).appHole? (ConLeche.nestCanonSub names (lps.map .param) n) 0 n with
    | some h =>
      obtain ⟨h3, h4⟩ := h1 h hh
      rw [h3]; exact h4.symm
    | none =>
      rw [h2 hh]
      rw [hh] at hocc
      simp only [nestOcc, Bool.or_eq_false_iff] at hocc
      simp only [instantiateLevelParams, iha hocc.1, ihx hocc.2]
  | lam t body m iht ihb =>
    intro hocc
    simp only [replaceApps, nestOcc, Bool.or_eq_false_iff] at hocc
    simp only [instantiateLevelParams, replaceApps, iht hocc.1, ihb hocc.2]
  | forallE t body m iht ihb =>
    intro hocc
    simp only [replaceApps, nestOcc, Bool.or_eq_false_iff] at hocc
    simp only [instantiateLevelParams, replaceApps, iht hocc.1, ihb hocc.2]
  | letE t v body iht ihv ihb =>
    intro hocc
    simp only [replaceApps, nestOcc, Bool.or_eq_false_iff] at hocc
    simp only [instantiateLevelParams, replaceApps, iht hocc.1.1, ihv hocc.1.2, ihb hocc.2]
  | proj s i x ih =>
    intro hocc
    simp only [replaceApps, nestOcc] at hocc
    simp only [instantiateLevelParams, replaceApps, ih hocc]
  | bvar i => intro _; rfl
  | fvar i ty _ => intro _; rfl
  | sort u => intro _; rfl
  | lit l => intro _; rfl

/-- **Two replacements that hit the same nodes agree after the variable
replacement** when their images do, on a term whose variables lie below
`n`, where the variable replacements agree. -/
theorem replaceApps_replaceFVars_congr {f₁ f₂ : Name → List Level → Option Expr}
    {g₁ g₂ : Nat → Option Expr} {b k n : Nat}
    (hsame : ∀ c us, (f₁ c us).isSome = (f₂ c us).isSome)
    (himg : ∀ c us h₁ h₂, f₁ c us = some h₁ → f₂ c us = some h₂ →
      h₁.replaceFVars g₁ = h₂.replaceFVars g₂)
    (hg : ∀ i, i < n → g₁ i = g₂ i) :
    ∀ t : Expr, t.fvarsBelow n →
      (t.replaceApps f₁ b k).replaceFVars g₁ = (t.replaceApps f₂ b k).replaceFVars g₂ := by
  have hnode : ∀ e : Expr,
      (∀ h₁, e.appHole? f₁ b k = some h₁ → ∃ h₂, e.appHole? f₂ b k = some h₂ ∧
        h₁.replaceFVars g₁ = h₂.replaceFVars g₂) ∧
      (e.appHole? f₁ b k = none → e.appHole? f₂ b k = none) := by
    intro e
    unfold appHole?
    cases e.phApp? b k with
    | none => simp
    | some p =>
      simp only [Option.bind_some]
      have hs := hsame p.1 p.2
      constructor
      · intro h₁ hh
        obtain ⟨h₂, hh₂⟩ := Option.isSome_iff_exists.mp (by rw [← hs, hh]; rfl)
        exact ⟨h₂, hh₂, himg _ _ _ _ hh hh₂⟩
      · intro hh
        rw [hh] at hs
        cases hf : f₂ p.1 p.2 with
        | none => rfl
        | some _ => rw [hf] at hs; exact nomatch hs
  intro t
  induction t with
  | const c v =>
    intro _
    rw [replaceApps_const, replaceApps_const]
    obtain ⟨h1, h2⟩ := hnode (.const c v)
    cases hh : (Expr.const c v).appHole? f₁ b k with
    | some h =>
      obtain ⟨h', hh', he⟩ := h1 h hh
      rw [hh']; exact he
    | none => rw [h2 hh]; rfl
  | app a x iha ihx =>
    intro hb
    simp only [fvarsBelow] at hb
    rw [replaceApps_app, replaceApps_app]
    obtain ⟨h1, h2⟩ := hnode (.app a x)
    cases hh : (Expr.app a x).appHole? f₁ b k with
    | some h =>
      obtain ⟨h', hh', he⟩ := h1 h hh
      rw [hh']; exact he
    | none =>
      rw [h2 hh]
      simp only [replaceFVars, iha hb.1, ihx hb.2]
  | lam t body m iht ihb =>
    intro hb; simp only [fvarsBelow] at hb
    simp only [replaceApps, replaceFVars, iht hb.1, ihb hb.2]
  | forallE t body m iht ihb =>
    intro hb; simp only [fvarsBelow] at hb
    simp only [replaceApps, replaceFVars, iht hb.1, ihb hb.2]
  | letE t v body iht ihv ihb =>
    intro hb; simp only [fvarsBelow] at hb
    simp only [replaceApps, replaceFVars, iht hb.1, ihv hb.2.1, ihb hb.2.2]
  | proj s i x ih =>
    intro hb; simp only [fvarsBelow] at hb
    simp only [replaceApps, replaceFVars, ih hb]
  | bvar i => intro _; rfl
  | fvar i ty _ =>
    intro hb
    simp only [fvarsBelow] at hb
    simp only [replaceApps, replaceFVars, hg i hb]
  | sort u => intro _; rfl
  | lit l => intro _; rfl

/-- **Parallel substitution is a variable replacement** on a term whose
variables lie below its range. -/
theorem substFvars_eq_replaceFVars {b D : Nat} {s : Nat → Expr} :
    ∀ t : Expr, t.fvarsBelow b →
      substFvars b D s t = t.replaceFVars fun i => if i < b then some (s i) else none := by
  intro t
  induction t with
  | fvar i ty _ =>
    intro hb
    simp only [fvarsBelow] at hb
    simp [substFvars, replaceFVars, hb]
  | app a x iha ihx =>
    intro hb; simp only [fvarsBelow] at hb
    simp only [substFvars, replaceFVars, iha hb.1, ihx hb.2]
  | lam t body m iht ihb =>
    intro hb; simp only [fvarsBelow] at hb
    simp only [substFvars, replaceFVars, iht hb.1, ihb hb.2]
  | forallE t body m iht ihb =>
    intro hb; simp only [fvarsBelow] at hb
    simp only [substFvars, replaceFVars, iht hb.1, ihb hb.2]
  | letE t v body iht ihv ihb =>
    intro hb; simp only [fvarsBelow] at hb
    simp only [substFvars, replaceFVars, iht hb.1, ihv hb.2.1, ihb hb.2.2]
  | proj s' i x ih =>
    intro hb; simp only [fvarsBelow] at hb
    simp only [substFvars, replaceFVars, ih hb]
  | bvar i => intro _; rfl
  | sort u => intro _; rfl
  | const c v => intro _; rfl
  | lit l => intro _; rfl

/-- **The container substitution law, syntactically** (see the section
header): the frame's constructor type at the key `(us, ds)`, its group
`gnames` (the recorded block's members `names`, in any order) abstracted
to the frame's `holes`, is the recorded canonical abstraction at the
levels `us`, its canonical parameter variables substituted by `ds` and
each canonical hole by the frame's hole of the same member. -/
theorem frameCrest_eq {names gnames lps : List Name} {n : Nat} {us : List Level}
    {ds holes : List Expr} {b D : Nat} {s : Nat → Expr}
    (hb : b = n + names.length) (hlv : (lps.map Level.param).map (Level.subst lps us) = us)
    (hdlen : ds.length = n) (hmemG : ∀ c, c ∈ gnames ↔ c ∈ names)
    (hpar : ∀ i, i < n → s i = ds.getD i default)
    (hhole : ∀ mm, mm < names.length →
      s (n + mm) = holes.getD (gnames.idxOf (names.getD mm .anonymous)) default)
    (hhl : gnames.length ≤ holes.length)
    {e A : Expr} (he : e.hasFvar = false) (hocc : A.nestOcc names 0 0 = false)
    (hA : ConLeche.nestCanonCrest names (lps.map .param) n e = some A) :
    ConLeche.nestCrest gnames us ds holes (e.instantiateLevelParams lps us)
      = some (substFvars b D s (A.instantiateLevelParams lps us)) := by
  unfold ConLeche.nestCanonCrest at hA
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hA
  have htL : ConLeche.instPisWith (ConLeche.nestPhs n) (e.instantiateLevelParams lps us)
      = some (t.instantiateLevelParams lps us) := by
    have := instPisWith_instantiateLevelParams lps us (ConLeche.nestPhs n)
      (fun a ha => by
        simp only [ConLeche.nestPhs, List.mem_map] at ha
        obtain ⟨i, -, rfl⟩ := ha
        exact ⟨_, _, rfl⟩) ht
    rwa [nestPhs_instantiateLevelParams] at this
  -- the instantiated type's variables are the canonical parameters
  have htw : WScoped n t :=
    ConLeche.wscoped_instPisWith (fun a ha => by
        simp only [ConLeche.nestPhs, List.mem_map, List.mem_range] at ha
        obtain ⟨i, hi, rfl⟩ := ha
        simp only [WScoped]
        exact ⟨hi, by simp⟩)
      (WScoped.of_not_hasFvar he) ht
  have htb : fvarsBelow n (t.instantiateLevelParams lps us) :=
    fvarsBelow_instantiateLevelParams' lps us htw.fvarsBelow
  -- the recorded abstraction's variables are the canonical parameters and holes
  have hAb : fvarsBelow b
      ((t.replaceApps (ConLeche.nestCanonSub names (lps.map .param) n) 0 n).instantiateLevelParams
        lps us) := by
    refine fvarsBelow_instantiateLevelParams' lps us (WScoped.fvarsBelow
      (WScoped_of_leaves _ fun l hl => ?_))
    obtain ⟨i, hi, rfl⟩ := ConLeche.fvarLeaves_nestCanonCrest he
      (by unfold ConLeche.nestCanonCrest; rw [ht]; rfl) l hl
    exact ⟨by omega, by simp [WScoped]⟩
  unfold ConLeche.nestCrest ConLeche.nestCanonCrest
  rw [hdlen, htL]
  simp only [Option.map_some, Option.some.injEq]
  rw [substFvars_eq_replaceFVars _ hAb,
    ← replaceApps_canon_instantiateLevelParams hlv t hocc]
  refine replaceApps_replaceFVars_congr (fun c v => ?_) (fun c v h₁ h₂ hh₁ hh₂ => ?_)
    (fun i hi => ?_) _ htb
  · simp only [nestCanonSub_eq, hmemG]
    split <;> rfl
  · rw [nestCanonSub_eq] at hh₁ hh₂
    split at hh₁
    · rename_i hcg
      have hc : c ∈ names := (hmemG c).mp hcg.2
      rw [if_pos ⟨hcg.1, hc⟩] at hh₂
      cases hh₁; cases hh₂
      have hig := List.idxOf_lt_length_of_mem hcg.2
      have hin := List.idxOf_lt_length_of_mem hc
      simp only [replaceFVars, ConLeche.nestKeyMap, hdlen, show ¬ n + gnames.idxOf c < n by omega,
        if_false, show n + gnames.idxOf c - n = gnames.idxOf c by omega,
        show n + names.idxOf c < b by omega, if_true, Option.getD_some]
      have hc' : names.getD (names.idxOf c) .anonymous = c := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some,
          List.getElem_idxOf]
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hhole _ hin, hc',
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    · exact nomatch hh₁
  · simp only [ConLeche.nestKeyMap, hdlen, hi, if_true, show i < b by omega, hpar i hi,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < ds.length by omega),
      Option.getD_some]

end ConLeche.Expr
