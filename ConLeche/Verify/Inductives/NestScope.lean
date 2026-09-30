module

public import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Verify.Shift
import ConLeche.Verify.Leaves
public import ConLeche.Verify.Inductives.ReplaceApps
import ConLeche.Verify.InstLevels

public section

/-!
# The positivity walk's scoping

What both the cached simulation (`Verify/Cached/NestPosC.lean`) and the
model's consumer (`Model/Inductives/BlockPosRun.lean`) need of the terms
the walk reads: the member holes are variables above the parameters,
and a member constructor's abstracted type, instantiated at the
canonical parameters, is well scoped at the walk's depth.
-/

namespace ConLeche

open Expr

/-! ## Scoping -/

/-- A well-scoped term whose variables lie below `d'` is well scoped
there. -/
theorem WScoped.of_fvarsBelow : ∀ {e : Expr} {d d' : Nat}, WScoped d e →
    Expr.fvarsBelow d' e → WScoped d' e := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro d d' hw hb
    simp only [WScoped] at hw ⊢
    exact ⟨hb, hw.2⟩
  | app f a ihf iha =>
    intro d d' hw hb
    simp only [WScoped, Expr.fvarsBelow] at hw hb ⊢
    exact ⟨ihf hw.1 hb.1, iha hw.2 hb.2⟩
  | lam ty b m iht ihb =>
    intro d d' hw hb
    simp only [WScoped, Expr.fvarsBelow] at hw hb ⊢
    exact ⟨iht hw.1 hb.1, ihb hw.2 hb.2⟩
  | forallE ty b m iht ihb =>
    intro d d' hw hb
    simp only [WScoped, Expr.fvarsBelow] at hw hb ⊢
    exact ⟨iht hw.1 hb.1, ihb hw.2 hb.2⟩
  | letE ty v b iht ihv ihb =>
    intro d d' hw hb
    simp only [WScoped, Expr.fvarsBelow] at hw hb ⊢
    exact ⟨iht hw.1 hb.1, ihv hw.2.1 hb.2.1, ihb hw.2.2 hb.2.2⟩
  | proj s i e ih =>
    intro d d' hw hb
    simp only [WScoped, Expr.fvarsBelow] at hw hb ⊢
    exact ih hw hb
  | bvar _ => intros; simp [WScoped]
  | sort _ => intros; simp [WScoped]
  | const _ _ => intros; simp [WScoped]
  | lit _ => intros; simp [WScoped]

/-- Replacing constants of a closed term by well-scoped terms gives a
well-scoped term. -/
theorem WScoped.replaceConsts_closed {f : Name → List Level → Option Expr} {d : Nat}
    (hf : ∀ c us e, f c us = some e → WScoped d e) :
    ∀ (e : Expr), e.hasFvar = false → WScoped d (e.replaceConsts f) := by
  intro e
  induction e with
  | fvar idx ty _ => intro h; simp [Expr.hasFvar] at h
  | const c us =>
    intro _
    simp only [Expr.replaceConsts]
    cases hc : f c us with
    | none => simp [WScoped]
    | some e => exact hf c us e hc
  | app f a ihf iha =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, WScoped]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b m iht ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, WScoped]
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b m iht ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, WScoped]
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, WScoped]
    exact ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | proj s i e ih =>
    intro h
    simp only [Expr.hasFvar] at h
    simp only [Expr.replaceConsts, WScoped]
    exact ih h
  | bvar _ => intro _; simp [Expr.replaceConsts, WScoped]
  | sort _ => intro _; simp [Expr.replaceConsts, WScoped]
  | lit _ => intro _; simp [Expr.replaceConsts, WScoped]

/-- A context whose stored constants are closed. -/
@[expose] def NestCtxOk (ctx : NestCtx) : Prop :=
  ∀ n ci, ctx.find? n = some ci → ci.toConstantVal.type.hasFvar = false

/-- A constructor entry is its constructor record. -/
theorem nestCtorEntry_some {C : Name} {ci : ConstantInfo} {y : ConstantVal × Nat × Nat}
    (h : nestCtorEntry C ci = some y) : ci = .ctorInfo y.1 y.2.1 y.2.2 := by
  unfold nestCtorEntry at h
  split at h
  · split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h; rfl
        · exact nomatch h
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- **A container's constructors are stored constructors** (looked up by
the recorded names). -/
theorem nestContainer_mem {ctx : NestCtx} {C : Name} {nP : Nat} {L : List (ConstantVal × Nat)}
    (h : nestContainer ctx C = some (nP, L)) :
    ∀ x ∈ L, ∃ n nPc, ctx.find? n = some (.ctorInfo x.1 nPc x.2) := by
  unfold nestContainer at h
  split at h
  · rename_i caps _
    dsimp only at h
    generalize hcs : List.filterMap _ caps.ctors = cs at h
    have hall : ∀ y ∈ cs, ∃ n, ctx.find? n = some (.ctorInfo y.1 y.2.1 y.2.2) := by
      intro y hy
      rw [← hcs] at hy
      obtain ⟨n, -, hn⟩ := List.mem_filterMap.mp hy
      cases hf : ctx.find? n with
      | none => rw [hf] at hn; exact nomatch hn
      | some ci =>
        rw [hf, Option.bind_some] at hn
        exact ⟨n, by rw [hf, nestCtorEntry_some hn]⟩
    cases cs with
    | nil =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      intro x hx; exact nomatch hx
    | cons y0 rest =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨n, hn⟩ := hall y hy
      exact ⟨n, y.2.1, hn⟩
  · exact nomatch h

/-- An `Option` `mapM`'s outputs come from its inputs. -/
theorem option_mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ y ∈ l', ∃ x ∈ l, f x = some y
  | [], l', h, y, hy => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact nomatch hy
  | a :: l, l', h, y, hy => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => rw [hfa] at h; exact nomatch h
    | some b =>
      rw [hfa] at h
      cases hl : l.mapM f with
      | none => simp [hl] at h
      | some bs =>
        simp only [hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a, List.mem_cons_self, hfa⟩
        · obtain ⟨x, hx, hfx⟩ := option_mapM_mem hl y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-- The member holes are variables, well scoped above them (their types
are the formers at the canonical parameters). -/
theorem nestHoles_ok {ctx : NestCtx} (hc : NestCtxOk ctx)
    (hpar : ∀ x ∈ ctx.params, WScoped ctx.nP x) {holes : List Expr}
    (h : nestHoles ctx = some holes) :
    ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty := by
  intro x hx
  obtain ⟨mm, hmm, hf⟩ := option_mapM_mem h x hx
  have hmm' := List.mem_range.mp hmm
  split at hf
  · next cv caps hfind =>
    obtain ⟨ty, hty, rfl⟩ := Option.map_eq_some_iff.mp hf
    refine ⟨?_, _, _, rfl⟩
    simp only [WScoped, NestCtx.hiAt]
    refine ⟨by omega, WScoped.mono (by omega) (wscoped_instPisWith hpar
      (WScoped.of_not_hasFvar (hc _ _ hfind)) hty)⟩
  · exact nomatch hf

/-- A member constructor's root crest is well scoped at the walk's depth. -/
theorem rootCrest_wscoped {ctx : NestCtx} {holes : List Expr}
    (hholes : ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty)
    (hlen : ctx.names.length ≤ holes.length)
    (hpar : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x) {cv : ConstantVal} {crest : Expr}
    (hcl : cv.type.hasFvar = false)
    (h : nestCrest ctx.names (ctx.lps.map .param) ctx.params holes
      (cv.type.instantiateLevelParams cv.levelParams (ctx.lps.map .param)) = some crest) :
    WScoped (ctx.hiAt 0) crest :=
  WScoped_nestCrest (by rw [hasFvar_instantiateLevelParams]; exact hcl) hlen
    (fun x hx => (List.mem_append.mp hx).elim (hpar x) (fun h => (hholes x h).1)) h

/-! ## The abstracted, instantiated constructor type: leaves and bounds -/

/-- The leaves of a closed term with constants replaced are the
replacements' leaves. -/
theorem fvarLeaves_replaceConsts_closed {f : Name → List Level → Option Expr} :
    ∀ (e : Expr), e.hasFvar = false → ∀ l ∈ (e.replaceConsts f).fvarLeaves,
      ∃ c us r, f c us = some r ∧ l ∈ r.fvarLeaves := by
  intro e
  induction e with
  | bvar i => intro _ l hl; simp [Expr.replaceConsts, fvarLeaves] at hl
  | fvar idx ty _ => intro h; simp [Expr.hasFvar] at h
  | sort u => intro _ l hl; simp [Expr.replaceConsts, fvarLeaves] at hl
  | lit v => intro _ l hl; simp [Expr.replaceConsts, fvarLeaves] at hl
  | const c us =>
    intro _ l hl
    simp only [Expr.replaceConsts] at hl
    cases hc : f c us with
    | none => rw [hc] at hl; simp [fvarLeaves] at hl
    | some r => rw [hc] at hl; exact ⟨c, us, r, hc, hl⟩
  | app a b iha ihb =>
    intro h l hl
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact iha h.1 l hl
    · exact ihb h.2 l hl
  | lam ty b m iht ihb =>
    intro h l hl
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact iht h.1 l hl
    · exact ihb h.2 l hl
  | forallE ty b m iht ihb =>
    intro h l hl
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact iht h.1 l hl
    · exact ihb h.2 l hl
  | letE ty v b iht ihv ihb =>
    intro h l hl
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact iht h.1.1 l hl
    · exact ihv h.1.2 l hl
    · exact ihb h.2 l hl
  | proj s i e ihe =>
    intro h l hl
    simp only [Expr.hasFvar] at h
    simp only [Expr.replaceConsts, fvarLeaves] at hl
    exact ihe h l hl

/-- Replacing constants by closed terms keeps the loose-bvar bound. -/
theorem looseBVarsBounded_replaceConsts {f : Name → List Level → Option Expr}
    (hf : ∀ c us r, f c us = some r → r.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      (e.replaceConsts f).looseBVarsBounded k = true := by
  intro e
  induction e with
  | bvar i => intro k h; simpa [Expr.replaceConsts] using h
  | fvar idx ty _ => intro k _; simp [Expr.replaceConsts, looseBVarsBounded]
  | sort u => intro k _; simp [Expr.replaceConsts, looseBVarsBounded]
  | lit v => intro k _; simp [Expr.replaceConsts, looseBVarsBounded]
  | const c us =>
    intro k _
    simp only [Expr.replaceConsts]
    cases hc : f c us with
    | none => simp [looseBVarsBounded]
    | some r => exact looseBVarsBounded_mono (Nat.zero_le k) (hf c us r hc)
  | app a b iha ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceConsts, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iha k h.1, ihb k h.2⟩
  | lam ty b m iht ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceConsts, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b m iht ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceConsts, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty v b iht ihv ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceConsts, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i e ihe =>
    intro k h
    simp only [looseBVarsBounded] at h
    simp only [Expr.replaceConsts, looseBVarsBounded]
    exact ihe k h

/-- A Π-telescope instantiated at bvar-closed arguments stays bvar-closed. -/
theorem looseBVarsBounded_instPisWith :
    ∀ {as : List Expr} {e r : Expr}, (∀ a ∈ as, a.looseBVarsBounded 0 = true) →
      e.looseBVarsBounded 0 = true → instPisWith as e = some r →
      r.looseBVarsBounded 0 = true
  | [], e, r, _, he, h => by
    simp only [instPisWith, Option.some.injEq] at h
    subst h; exact he
  | a :: as, e, r, ha, he, h => by
    match e, he, h with
    | .forallE t b m, he, h =>
      have h' : instPisWith as (b.instantiate1 a) = some r := h
      simp only [looseBVarsBounded, Bool.and_eq_true] at he
      exact looseBVarsBounded_instPisWith (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (looseBVarsBounded_instantiate1_gen (ha a List.mem_cons_self) he.2) h'

/-- An `Option` `mapM`'s output, positionally. -/
theorem option_mapM_getElem? {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      ∀ (i : Nat) (x : α), l[i]? = some x → ∃ y, f x = some y ∧ l'[i]? = some y
  | [], _, _, i, x, hx => by simp at hx
  | a :: l, l', h, i, x, hx => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => rw [hfa] at h; exact nomatch h
    | some b =>
      rw [hfa] at h
      cases hl : l.mapM f with
      | none => simp [hl] at h
      | some bs =>
        simp only [hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          exact ⟨b, hfa, rfl⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx ⊢
          exact option_mapM_getElem? hl i x hx

/-- **Member `t`'s hole** is the variable `nP + t` carrying the member's
stored type at the canonical parameters. -/
theorem nestHoles_getElem? {ctx : NestCtx} {holes : List Expr} (h : nestHoles ctx = some holes)
    {t : Nat} (ht : t < ctx.names.length) :
    ∃ cv caps ty, ctx.find? (ctx.names.getD t .anonymous) = some (.indInfo cv caps) ∧
      instPisWith ctx.params cv.type = some ty ∧ holes[t]? = some (.fvar (ctx.nP + t) ty) := by
  obtain ⟨y, hy, hget⟩ := option_mapM_getElem? h t t (List.getElem?_range ht)
  split at hy
  · next cv caps hfind =>
    obtain ⟨ty, hty, rfl⟩ := Option.map_eq_some_iff.mp hy
    exact ⟨cv, caps, ty, hfind, hty, hget⟩
  · exact nomatch hy

/-- An `Option` `mapM` keeps the length. -/
theorem option_mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => rw [hfa] at h; exact nomatch h
    | some b =>
      rw [hfa] at h
      cases hl : l.mapM f with
      | none => simp [hl] at h
      | some bs =>
        simp only [hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        simp [option_mapM_length hl]

/-- One hole per member. -/
theorem nestHoles_length {ctx : NestCtx} {holes : List Expr} (h : nestHoles ctx = some holes) :
    holes.length = ctx.names.length := by
  rw [option_mapM_length h, List.length_range]

/-- Every hole is a member's variable, carrying the member's stored type
at the canonical parameters. -/
theorem nestHoles_mem {ctx : NestCtx} {holes : List Expr} (h : nestHoles ctx = some holes) :
    ∀ x ∈ holes, ∃ i cv caps ty, ctx.find? (ctx.names.getD i .anonymous) = some (.indInfo cv caps) ∧
      instPisWith ctx.params cv.type = some ty ∧ x = .fvar (ctx.nP + i) ty := by
  intro x hx
  obtain ⟨mm, -, hf⟩ := option_mapM_mem h x hx
  split at hf
  · next cv caps hfind =>
    obtain ⟨ty, hty, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact ⟨mm, cv, caps, ty, hfind, hty, rfl⟩
  · exact nomatch hf

/-! ## The seeds: their keys

A seed (`nestSeedOf`) is a class the recursor check resolved, moved to
the walk's representation: its parameters' members abstracted to their
holes and every free variable — below the parameter count — replaced
WHOLE by the canonical parameter variable of its index.  So the only
free variables of a seed's parameter are canonical variables and holes,
each whole: its leaves are theirs, and it is well scoped wherever they
are. -/

/-- **Whole applications to whole variables, then variables to whole
terms**: when every image is a variable `g` replaces, and every variable
of `x` (below `n`) is replaced, every leaf of the result is a
replacement's. -/
theorem fvarLeaves_replaceApps_replaceFVars_whole {f : Name → List Level → Option Expr}
    {g : Nat → Option Expr} {b k n : Nat}
    (hf : ∀ c us h, f c us = some h → ∃ i ty, h = .fvar i ty ∧ (g i).isSome = true)
    (hgn : ∀ i, i < n → (g i).isSome = true) :
    ∀ (x : Expr), x.fvarsBelow n → ∀ l ∈ ((x.replaceApps f b k).replaceFVars g).fvarLeaves,
      ∃ i a, g i = some a ∧ l ∈ a.fvarLeaves := by
  have himg : ∀ (e h : Expr), e.appHole? f b k = some h → ∀ l ∈ (h.replaceFVars g).fvarLeaves,
      ∃ i a, g i = some a ∧ l ∈ a.fvarLeaves := by
    intro e h hh l hl
    obtain ⟨c, us, hc⟩ := Expr.appHole?_some hh
    obtain ⟨i, ty, rfl, hgi⟩ := hf c us _ hc
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hgi
    simp only [Expr.replaceFVars, ha, Option.getD_some] at hl
    exact ⟨i, a, ha, hl⟩
  intro x
  induction x with
  | bvar i => intro _ l hl; simp [Expr.replaceApps, Expr.replaceFVars, fvarLeaves] at hl
  | sort u => intro _ l hl; simp [Expr.replaceApps, Expr.replaceFVars, fvarLeaves] at hl
  | lit v => intro _ l hl; simp [Expr.replaceApps, Expr.replaceFVars, fvarLeaves] at hl
  | fvar idx ty _ =>
    intro hb l hl
    simp only [Expr.fvarsBelow] at hb
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hgn idx hb)
    simp only [Expr.replaceApps, Expr.replaceFVars, ha, Option.getD_some] at hl
    exact ⟨idx, a, ha, hl⟩
  | const c us =>
    intro _ l hl
    rw [Expr.replaceApps_const] at hl
    split at hl
    · rename_i h hh; exact himg _ _ hh l hl
    · simp [Expr.replaceFVars, fvarLeaves] at hl
  | app a x iha ihx =>
    intro hb l hl
    rw [Expr.replaceApps_app] at hl
    split at hl
    · rename_i h hh; exact himg _ _ hh l hl
    · simp only [Expr.fvarsBelow] at hb
      simp only [Expr.replaceFVars, fvarLeaves, List.mem_append] at hl
      exact hl.elim (iha hb.1 l) (ihx hb.2 l)
  | lam t body m iht ihb =>
    intro hb l hl
    simp only [Expr.fvarsBelow] at hb
    simp only [Expr.replaceApps, Expr.replaceFVars, fvarLeaves, List.mem_append] at hl
    exact hl.elim (iht hb.1 l) (ihb hb.2 l)
  | forallE t body m iht ihb =>
    intro hb l hl
    simp only [Expr.fvarsBelow] at hb
    simp only [Expr.replaceApps, Expr.replaceFVars, fvarLeaves, List.mem_append] at hl
    exact hl.elim (iht hb.1 l) (ihb hb.2 l)
  | letE t v body iht ihv ihb =>
    intro hb l hl
    simp only [Expr.fvarsBelow] at hb
    simp only [Expr.replaceApps, Expr.replaceFVars, fvarLeaves, List.mem_append] at hl
    exact hl.elim (·.elim (iht hb.1 l) (ihv hb.2.1 l)) (ihb hb.2.2 l)
  | proj s i x ih =>
    intro hb l hl
    simp only [Expr.fvarsBelow] at hb
    simp only [Expr.replaceApps, Expr.replaceFVars, fvarLeaves] at hl
    exact ih hb l hl

/-- **A seed's parameters** (`nestSeedOf`): at a walk context whose
canonical variables are `nP` in number, every parameter of a class whose
free variables lie below `nP` has its leaves among the canonical
variables' and the holes', and is well scoped at the walk's depth where
the canonical variables and the holes are. -/
theorem nestSeedOf_ds {ctx : NestCtx} {holes : List Expr} (hh : nestHoles ctx = some holes)
    (hlen : ctx.params.length = ctx.nP) {I : Name} {us : List Level} {ds : List Expr}
    {nPc : Nat} (hds : ∀ x ∈ ds, x.fvarsBelow ctx.nP) :
    ∀ y ∈ (nestSeedOf ctx holes I us ds nPc).1.ds,
      (∀ l ∈ y.fvarLeaves, ∃ a ∈ ctx.params ++ holes, l ∈ a.fvarLeaves) ∧
      ((∀ x ∈ holes, WScoped (ctx.hiAt 0) x) → (∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x) →
        WScoped (ctx.hiAt 0) y) := by
  intro y hy
  simp only [nestSeedOf, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hL : ∀ l ∈ ((x.replaceApps (nestCanonSub ctx.names (ctx.lps.map .param) ctx.nP) 0
      ctx.nP).replaceFVars (nestKeyMap ctx.params holes)).fvarLeaves,
      ∃ a ∈ ctx.params ++ holes, l ∈ a.fvarLeaves := by
    intro l hl
    obtain ⟨i, a, hg, hl'⟩ := fvarLeaves_replaceApps_replaceFVars_whole (n := ctx.nP)
      (fun c us' h hc => by
        obtain ⟨m, hm, -, -, rfl⟩ := nestCanonSub_some hc
        refine ⟨_, _, rfl, ?_⟩
        simp [nestKeyMap, hlen, List.getElem?_eq_getElem
          (show m < holes.length by rw [nestHoles_length hh]; exact hm)])
      (fun i hi => by
        simp [nestKeyMap, hlen, hi])
      x (hds x hx) l hl
    unfold nestKeyMap at hg
    split at hg
    · exact ⟨a, List.mem_append_left _ (List.mem_of_getElem? hg), hl'⟩
    · exact ⟨a, List.mem_append_right _ (List.mem_of_getElem? hg), hl'⟩
  refine ⟨hL, fun hH hP => Expr.WScoped_of_leaves _ fun l hl => ?_⟩
  obtain ⟨a, ha, hla⟩ := hL l hl
  rcases List.mem_append.mp ha with ha | ha
  · exact WScoped_leaves a (hP a ha) l hla
  · exact WScoped_leaves a (hH a ha) l hla

/-- Replacing variables by closed terms keeps the loose-bvar bound. -/
theorem looseBVarsBounded_replaceFVars {g : Nat → Option Expr}
    (hg : ∀ i r, g i = some r → r.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      (e.replaceFVars g).looseBVarsBounded k = true := by
  intro e
  induction e with
  | bvar i => intro k h; simpa [Expr.replaceFVars] using h
  | fvar idx ty _ =>
    intro k _
    simp only [Expr.replaceFVars]
    cases hc : g idx with
    | none => simp [looseBVarsBounded]
    | some r => exact looseBVarsBounded_mono (Nat.zero_le k) (hg idx r hc)
  | sort u => intro k _; simp [Expr.replaceFVars, looseBVarsBounded]
  | lit v => intro k _; simp [Expr.replaceFVars, looseBVarsBounded]
  | const c us => intro k _; simp [Expr.replaceFVars, looseBVarsBounded]
  | app a b iha ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceFVars, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iha k h.1, ihb k h.2⟩
  | lam ty b m iht ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceFVars, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b m iht ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceFVars, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty v b iht ihv ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceFVars, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i e ihe =>
    intro k h
    simp only [looseBVarsBounded] at h
    simp only [Expr.replaceFVars, looseBVarsBounded]
    exact ihe k h

/-- **A seed's parameters are closed** under binders: the class's are,
and the holes and the canonical variables they are replaced by are
variables. -/
theorem nestSeedOf_closed {ctx : NestCtx} {holes : List Expr} (hh : nestHoles ctx = some holes)
    (hparF : ∀ a ∈ ctx.params, ∃ i ty, a = .fvar i ty) {I : Name} {us : List Level}
    {ds : List Expr} {nPc : Nat} (hds : ∀ x ∈ ds, x.looseBVarsBounded 0 = true) :
    ∀ y ∈ (nestSeedOf ctx holes I us ds nPc).1.ds, y.looseBVarsBounded 0 = true := by
  intro y hy
  simp only [nestSeedOf, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  refine looseBVarsBounded_replaceFVars (fun i r hr => ?_) _ 0
    (Expr.looseBVarsBounded_replaceApps (fun c us' r hr => ?_) x 0 (hds x hx))
  · unfold nestKeyMap at hr
    split at hr
    · obtain ⟨j, ty, rfl⟩ := hparF r (List.mem_of_getElem? hr)
      simp [looseBVarsBounded]
    · obtain ⟨j, cv, caps, ty, -, -, rfl⟩ := nestHoles_mem hh r (List.mem_of_getElem? hr)
      simp [looseBVarsBounded]
  · obtain ⟨m, -, -, -, rfl⟩ := nestCanonSub_some hr
    simp [looseBVarsBounded]

end ConLeche
