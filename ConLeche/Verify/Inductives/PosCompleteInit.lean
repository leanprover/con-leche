module

public import ConLeche.Verify.Inductives.PosComplete
import ConLeche.Verify.Shift
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Cached.Erase

public section

/-!
# The σ-relation holds before the first whnf (lane COMPLETE-2, (A) at the root)

At a member constructor the walk reads `instPisWith params (nestAbstract t)`
(the members abstracted to their holes, then the parameters instantiated)
and official reads `replace_all_nested (instantiate params t)`.  With the
elimination's FINAL auxiliary map `M` (`sigmaAll`: official's top-down
replacement, a pure function once every key is present), the two are
`SRel`-related at the empty frame stack (`srel_member_root`), the
auxiliary type of a fresh container instantiation being `M`'s entry for
its READ-BACK key (the holes back to the members).

The connection from `sigmaAll` to the stateful `elimNested` (the final
state's member constructors ARE `sigmaAll` of the declared ones) is NOT
proved here: it is the loop invariant "`m_nested_aux` only grows, a
processed type is never rewritten" — see the report.
-/

namespace ConLeche

open Expr

/-- **Official's replacement with a FIXED auxiliary map** (the
elimination's final `m_nested_aux`): `replace_all_nested` once every key it
meets is present. -/
@[expose] def sigmaAll (c : Official.ElimCtx) (mem : List Name) (M : List (Expr × Name)) :
    Expr → Expr
  | .app f a =>
    match Official.isNestedApp c mem (.app f a) with
    | .ok (some (I, us, np, args)) =>
      match M.lookup (Expr.mkAppN (.const I us) (args.take np)) with
      | some x => Expr.mkAppN (Expr.mkAppN (.const x c.lvls) c.ps) (args.drop np)
      | none => .app (sigmaAll c mem M f) (sigmaAll c mem M a)
    | _ => .app (sigmaAll c mem M f) (sigmaAll c mem M a)
  | .lam t b m => .lam (sigmaAll c mem M t) (sigmaAll c mem M b) m
  | .forallE t b m => .forallE (sigmaAll c mem M t) (sigmaAll c mem M b) m
  | .letE t v b => .letE (sigmaAll c mem M t) (sigmaAll c mem M v) (sigmaAll c mem M b)
  | .proj s i x => .proj s i (sigmaAll c mem M x)
  | e => e

/-- **Official's replacement on `u` succeeds against `M`**: no nested
occurrence has a loose bound variable in its parameters (official's
throw), and every one met is a key of `M`. -/
@[expose] def SigOk (c : Official.ElimCtx) (mem : List Name) (M : List (Expr × Name)) :
    Expr → Prop
  | .app f a =>
    match Official.isNestedApp c mem (.app f a) with
    | .ok (some (I, us, np, args)) =>
      (M.lookup (Expr.mkAppN (.const I us) (args.take np))).isSome = true
    | .ok none => SigOk c mem M f ∧ SigOk c mem M a
    | .error _ => False
  | .lam t b _ | .forallE t b _ => SigOk c mem M t ∧ SigOk c mem M b
  | .letE t v b => SigOk c mem M t ∧ SigOk c mem M v ∧ SigOk c mem M b
  | .proj _ _ x => SigOk c mem M x
  | _ => True

/-- **The walk's input shape**: every member constant at the block's own
levels (M2′), no auxiliary constant, and every free variable a parameter
whose annotation mentions no declared type. -/
@[expose] def Good (ctx : NestCtx) (isAux : Name → Bool) : Expr → Prop
  | .fvar i ty => i < ctx.nP ∧ ty.deepOcc (fun n => ctx.names.contains n || isAux n) = false ∧
      Good ctx isAux ty
  | .const n us => isAux n = false ∧ (ctx.names.contains n = true → us = ctx.lps.map .param)
  | .app f a => Good ctx isAux f ∧ Good ctx isAux a
  | .lam t b _ | .forallE t b _ => Good ctx isAux t ∧ Good ctx isAux b
  | .letE t v b => Good ctx isAux t ∧ Good ctx isAux v ∧ Good ctx isAux b
  | .proj _ _ x => Good ctx isAux x
  | _ => True

/-- The member holes: member `m` at `nP + m`, typed by a closed term. -/
@[expose] def HolesOk (ctx : NestCtx) (holes : List Expr) : Prop :=
  ∀ m, m < ctx.names.length → ∃ ty, holes[m]? = some (.fvar (ctx.nP + m) ty) ∧
    ty.hasFvar = false ∧ ty.looseBVarsBounded 0 = true

/-- A key read back: the holes back to their constants (`nestHoleConst`). -/
@[expose] def rbExpr (ctx : NestCtx) (k : NestKey) : Expr :=
  Expr.mkAppN (.const k.cname k.lvls) (k.ds.map (·.replaceFVars (nestHoleConst ctx [])))

section Lemmas

variable {ctx : NestCtx} {σ : SigmaCtx} {holes : List Expr}

theorem findIdx?_spec {names : List Name} {n : Name} {m : Nat}
    (h : names.findIdx? (· == n) = some m) : m < names.length ∧ names.getD m .anonymous = n := by
  obtain ⟨hm, hn, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  refine ⟨hm, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
  simpa using hn

theorem findIdx?_of_contains {names : List Name} {n : Name} (h : names.contains n = true) :
    ∃ m, names.findIdx? (· == n) = some m := by
  cases hf : names.findIdx? (· == n) with
  | some m => exact ⟨m, rfl⟩
  | none =>
    rw [List.findIdx?_eq_none_iff] at hf
    have hmem : n ∈ names := by simpa using h
    have := hf n hmem
    simp at this

/-- The abstraction at a constant. -/
theorem nestAbstract_const (hh : HolesOk ctx holes) (n : Name) (us : List Level) :
    (∃ m ty, ctx.names.contains n = true ∧ us = ctx.lps.map .param ∧ m < ctx.names.length ∧
      ctx.names.getD m .anonymous = n ∧ ty.hasFvar = false ∧ ty.looseBVarsBounded 0 = true ∧
      nestAbstract ctx holes (.const n us) = .fvar (ctx.nP + m) ty) ∨
    ((ctx.names.contains n = false ∨ us ≠ ctx.lps.map .param) ∧
      nestAbstract ctx holes (.const n us) = .const n us) := by
  unfold nestAbstract
  simp only [Expr.replaceConsts]
  by_cases hus : (us == ctx.lps.map .param) = true
  · rw [if_pos hus]
    cases hf : ctx.names.findIdx? (· == n) with
    | none =>
      right
      refine ⟨Or.inl ?_, rfl⟩
      cases hc : ctx.names.contains n
      · rfl
      · obtain ⟨m, hm⟩ := findIdx?_of_contains hc
        rw [hf] at hm; exact nomatch hm
    | some m =>
      obtain ⟨hm, hn⟩ := findIdx?_spec hf
      obtain ⟨ty, hty, hcl, hbv⟩ := hh m hm
      left
      refine ⟨m, ty, ?_, by simpa using hus, hm, hn, hcl, hbv, by simp [hty]⟩
      rw [← hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
      simp [List.getElem_mem hm]
  · rw [if_neg hus]
    right
    exact ⟨Or.inr (by simpa using hus), rfl⟩

/-- The abstraction fixes a term mentioning no member. -/
theorem nestAbstract_of_deepFree (hh : HolesOk ctx holes) {p : Name → Bool}
    (hp : ∀ n, ctx.names.contains n = true → p n = true) :
    ∀ (x : Expr), x.deepOcc p = false → nestAbstract ctx holes x = x := by
  intro x
  induction x with
  | const n us =>
    intro hx
    simp only [Expr.deepOcc] at hx
    rcases nestAbstract_const hh n us with ⟨m, ty, hc, -⟩ | ⟨-, h⟩
    · rw [hp n hc] at hx; exact nomatch hx
    · exact h
  | fvar i ty ih =>
    intro hx
    simp only [Expr.deepOcc] at hx
    have := ih hx
    unfold nestAbstract at this ⊢
    simp only [Expr.replaceConsts] at this ⊢
    rw [this]
  | app f a ihf iha =>
    intro hx
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hx
    have h1 := ihf hx.1; have h2 := iha hx.2
    unfold nestAbstract at h1 h2 ⊢
    simp only [Expr.replaceConsts] at h1 h2 ⊢
    rw [h1, h2]
  | lam t b m iht ihb | forallE t b m iht ihb =>
    intro hx
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hx
    have h1 := iht hx.1; have h2 := ihb hx.2
    unfold nestAbstract at h1 h2 ⊢
    simp only [Expr.replaceConsts] at h1 h2 ⊢
    rw [h1, h2]
  | letE t v b iht ihv ihb =>
    intro hx
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hx
    have h1 := iht hx.1.1; have h2 := ihv hx.1.2; have h3 := ihb hx.2
    unfold nestAbstract at h1 h2 h3 ⊢
    simp only [Expr.replaceConsts] at h1 h2 h3 ⊢
    rw [h1, h2, h3]
  | proj s i e ih =>
    intro hx
    simp only [Expr.deepOcc] at hx
    have := ih hx
    unfold nestAbstract at this ⊢
    simp only [Expr.replaceConsts] at this ⊢
    rw [this]
  | bvar _ => intro; rfl
  | sort _ => intro; rfl
  | lit _ => intro; rfl

theorem abs_app (f a : Expr) :
    nestAbstract ctx holes (.app f a) = .app (nestAbstract ctx holes f) (nestAbstract ctx holes a) := rfl
theorem abs_lam (t b : Expr) (m : BinderMeta) :
    nestAbstract ctx holes (.lam t b m) = .lam (nestAbstract ctx holes t) (nestAbstract ctx holes b) m := rfl
theorem abs_forallE (t b : Expr) (m : BinderMeta) :
    nestAbstract ctx holes (.forallE t b m) =
      .forallE (nestAbstract ctx holes t) (nestAbstract ctx holes b) m := rfl
theorem abs_letE (t v b : Expr) :
    nestAbstract ctx holes (.letE t v b) =
      .letE (nestAbstract ctx holes t) (nestAbstract ctx holes v) (nestAbstract ctx holes b) := rfl
theorem abs_proj (s : Name) (i : Nat) (x : Expr) :
    nestAbstract ctx holes (.proj s i x) = .proj s i (nestAbstract ctx holes x) := rfl
theorem abs_fvar (i : Nat) (ty : Expr) :
    nestAbstract ctx holes (.fvar i ty) = .fvar i (nestAbstract ctx holes ty) := rfl

theorem abs_mkAppN (f : Expr) : ∀ (args : List Expr),
    nestAbstract ctx holes (Expr.mkAppN f args) =
      Expr.mkAppN (nestAbstract ctx holes f) (args.map (nestAbstract ctx holes))
  | [] => rfl
  | a :: as => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl, abs_mkAppN _ as]
    rfl

/-- The relation is reflexive on a term mentioning no declared type
(annotations included) and no hole... restricted to parameter
variables. -/
theorem srel_refl_deepFree {prog : List NestHole} {act : List NestKey} :
    ∀ (x : Expr), Good ctx σ.isAux x →
      x.deepOcc (fun n => ctx.names.contains n || σ.isAux n) = false →
      SRel ctx σ prog act x x := by
  intro x
  induction x with
  | const n us =>
    intro hg hx
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hx
    exact .const hx.1 hx.2
  | fvar i ty ih =>
    intro hg hx
    simp only [Good] at hg
    simp only [Expr.deepOcc] at hx
    exact .fvar (Or.inl hg.1) (ih hg.2.2 hx)
  | app f a ihf iha =>
    intro hg hx
    simp only [Good] at hg
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hx
    exact .app (ihf hg.1 hx.1) (iha hg.2 hx.2)
  | lam t b m iht ihb =>
    intro hg hx
    simp only [Good] at hg
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hx
    exact .lam (iht hg.1 hx.1) (ihb hg.2 hx.2)
  | forallE t b m iht ihb =>
    intro hg hx
    simp only [Good] at hg
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hx
    exact .forallE (iht hg.1 hx.1) (ihb hg.2 hx.2)
  | letE t v b iht ihv ihb =>
    intro hg hx
    simp only [Good] at hg
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hx
    exact .letE (iht hg.1 hx.1.1) (ihv hg.2.1 hx.1.2) (ihb hg.2.2 hx.2)
  | proj s i e ih =>
    intro hg hx
    simp only [Good] at hg
    simp only [Expr.deepOcc] at hx
    exact .proj (ih hg hx)
  | bvar i => intro _ _; exact .bvar i
  | sort u => intro _ _; exact .sort u
  | lit l => intro _ _; exact .lit l

/-- A term the relation fixes on the σ side: the walk side is its
abstraction. -/
theorem srel_abs_self (hh : HolesOk ctx holes) (hlv : σ.lvls = ctx.lps.map .param)
    {prog : List NestHole} {act : List NestKey} :
    ∀ (x : Expr), Good ctx σ.isAux x → SRel ctx σ prog act (nestAbstract ctx holes x) x := by
  intro x
  induction x with
  | const n us =>
    intro hg
    simp only [Good] at hg
    rcases nestAbstract_const hh n us with ⟨m, ty, hc, hus, hm, hn, -, -, h⟩ | ⟨hno, h⟩
    · rw [h, hus, ← hlv, ← hn]
      exact .mem hm
    · rw [h]
      refine .const ?_ hg.1
      cases hc : ctx.names.contains n
      · rfl
      · rcases hno with hno | hno
        · rw [hc] at hno; exact nomatch hno
        · exact absurd (hg.2 hc) hno
  | fvar i ty ih =>
    intro hg
    simp only [Good] at hg
    rw [abs_fvar]
    refine .fvar (Or.inl hg.1) ?_
    rw [nestAbstract_of_deepFree hh (p := fun n => ctx.names.contains n || σ.isAux n)
      (fun n hn => by rw [hn, Bool.true_or]) ty hg.2.1]
    exact srel_refl_deepFree ty hg.2.2 hg.2.1
  | app f a ihf iha =>
    intro hg; simp only [Good] at hg; rw [abs_app]; exact .app (ihf hg.1) (iha hg.2)
  | lam t b m iht ihb =>
    intro hg; simp only [Good] at hg; rw [abs_lam]; exact .lam (iht hg.1) (ihb hg.2)
  | forallE t b m iht ihb =>
    intro hg; simp only [Good] at hg; rw [abs_forallE]; exact .forallE (iht hg.1) (ihb hg.2)
  | letE t v b iht ihv ihb =>
    intro hg; simp only [Good] at hg; rw [abs_letE]
    exact .letE (iht hg.1) (ihv hg.2.1) (ihb hg.2.2)
  | proj s i e ih =>
    intro hg; simp only [Good] at hg; rw [abs_proj]; exact .proj (ih hg)
  | bvar i => intro; exact .bvar i
  | sort u => intro; exact .sort u
  | lit l => intro; exact .lit l

theorem replaceFVars_app (f : Nat → Option Expr) (a b : Expr) :
    (Expr.app a b).replaceFVars f = .app (a.replaceFVars f) (b.replaceFVars f) := rfl

/-- **The read-back undoes the abstraction** on the walk's input. -/
theorem rb_abs (hh : HolesOk ctx holes) :
    ∀ (x : Expr), Good ctx σ.isAux x →
      (nestAbstract ctx holes x).replaceFVars (nestHoleConst ctx []) = x := by
  intro x
  induction x with
  | const n us =>
    intro hg
    rcases nestAbstract_const hh n us with ⟨m, ty, hc, hus, hm, hn, -, -, h⟩ | ⟨-, h⟩
    · rw [h]
      simp only [Expr.replaceFVars, nestHoleConst]
      rw [if_pos ⟨Nat.le_add_right _ _, by simp only [NestCtx.hiAt]; omega⟩]
      rw [Nat.add_sub_cancel_left, hn, hus]
      rfl
    · rw [h]; rfl
  | fvar i ty _ =>
    intro hg
    simp only [Good] at hg
    rw [abs_fvar, nestAbstract_of_deepFree hh (p := fun n => ctx.names.contains n || σ.isAux n)
      (fun n hn => by rw [hn, Bool.true_or]) ty hg.2.1]
    simp only [Expr.replaceFVars, nestHoleConst]
    rw [if_neg (by omega), if_neg (by simp [NestCtx.hiAt])]
    rfl
  | app f a ihf iha =>
    intro hg; simp only [Good] at hg
    rw [abs_app, replaceFVars_app, ihf hg.1, iha hg.2]
  | lam t b m iht ihb =>
    intro hg; simp only [Good] at hg
    rw [abs_lam]; simp only [Expr.replaceFVars]; rw [iht hg.1, ihb hg.2]
  | forallE t b m iht ihb =>
    intro hg; simp only [Good] at hg
    rw [abs_forallE]; simp only [Expr.replaceFVars]; rw [iht hg.1, ihb hg.2]
  | letE t v b iht ihv ihb =>
    intro hg; simp only [Good] at hg
    rw [abs_letE]; simp only [Expr.replaceFVars]; rw [iht hg.1, ihv hg.2.1, ihb hg.2.2]
  | proj s i e ih =>
    intro hg; simp only [Good] at hg
    rw [abs_proj]; simp only [Expr.replaceFVars]; rw [ih hg]
  | bvar _ => intro; rfl
  | sort _ => intro; rfl
  | lit _ => intro; rfl

/-- A member occurrence becomes a hole occurrence. -/
theorem nestOcc_abs (hh : HolesOk ctx holes) :
    ∀ (x : Expr), Good ctx σ.isAux x → x.nestOcc ctx.names 0 0 = true →
      (nestAbstract ctx holes x).nestOcc ctx.names ctx.nP (ctx.hiAt 0) = true := by
  intro x
  induction x with
  | const n us =>
    intro hg hx
    simp only [Good] at hg
    simp only [Expr.nestOcc] at hx
    rcases nestAbstract_const hh n us with ⟨m, ty, hc, hus, hm, hn, -, -, h⟩ | ⟨hno, h⟩
    · rw [h]
      simp only [Expr.nestOcc, NestCtx.hiAt]
      exact decide_eq_true ⟨by omega, by omega⟩
    · rcases hno with hno | hno
      · rw [hno] at hx; exact nomatch hx
      · exact absurd (hg.2 hx) hno
  | fvar i ty _ => intro _ hx; simp [Expr.nestOcc] at hx
  | app f a ihf iha =>
    intro hg hx; simp only [Good] at hg
    simp only [Expr.nestOcc, Bool.or_eq_true] at hx
    rw [abs_app]; simp only [Expr.nestOcc, Bool.or_eq_true]
    rcases hx with hx | hx
    · exact Or.inl (ihf hg.1 hx)
    · exact Or.inr (iha hg.2 hx)
  | lam t b m iht ihb =>
    intro hg hx; simp only [Good] at hg
    simp only [Expr.nestOcc, Bool.or_eq_true] at hx
    rw [abs_lam]; simp only [Expr.nestOcc, Bool.or_eq_true]
    rcases hx with hx | hx
    · exact Or.inl (iht hg.1 hx)
    · exact Or.inr (ihb hg.2 hx)
  | forallE t b m iht ihb =>
    intro hg hx; simp only [Good] at hg
    simp only [Expr.nestOcc, Bool.or_eq_true] at hx
    rw [abs_forallE]; simp only [Expr.nestOcc, Bool.or_eq_true]
    rcases hx with hx | hx
    · exact Or.inl (iht hg.1 hx)
    · exact Or.inr (ihb hg.2 hx)
  | letE t v b iht ihv ihb =>
    intro hg hx; simp only [Good] at hg
    simp only [Expr.nestOcc, Bool.or_eq_true] at hx
    rw [abs_letE]; simp only [Expr.nestOcc, Bool.or_eq_true]
    rcases hx with (hx | hx) | hx
    · exact Or.inl (Or.inl (iht hg.1 hx))
    · exact Or.inl (Or.inr (ihv hg.2.1 hx))
    · exact Or.inr (ihb hg.2.2 hx)
  | proj s i e ih =>
    intro hg hx; simp only [Good] at hg
    simp only [Expr.nestOcc] at hx
    rw [abs_proj]; simp only [Expr.nestOcc]
    exact ih hg hx
  | bvar _ => intro _ hx; simp [Expr.nestOcc] at hx
  | sort _ => intro _ hx; simp [Expr.nestOcc] at hx
  | lit _ => intro _ hx; simp [Expr.nestOcc] at hx

theorem SRel.mkAppN {prog : List NestHole} {act : List NestKey} {f f' : Expr}
    (hf : SRel ctx σ prog act f f') :
    ∀ {as as' : List Expr}, Rel2 (SRel ctx σ prog act) as as' →
      SRel ctx σ prog act (Expr.mkAppN f as) (Expr.mkAppN f' as') := by
  intro as as' h
  induction h generalizing f f' with
  | nil => exact hf
  | cons ha _ ih => exact ih (.app hf ha)

theorem mkAppN_append (f : Expr) : ∀ (as bs : List Expr),
    Expr.mkAppN f (as ++ bs) = Expr.mkAppN (Expr.mkAppN f as) bs
  | [], _ => rfl
  | a :: as, bs => by
    rw [List.cons_append]
    exact mkAppN_append (.app f a) as bs

theorem wscoped_mkAppN {d : Nat} : ∀ {f : Expr} {as : List Expr}, Expr.WScoped d (Expr.mkAppN f as) →
    Expr.WScoped d f ∧ ∀ a ∈ as, Expr.WScoped d a
  | _, [], h => ⟨h, fun _ ha => nomatch ha⟩
  | f, a :: as, h => by
    obtain ⟨h1, h2⟩ := wscoped_mkAppN (f := .app f a) (as := as) h
    simp only [Expr.WScoped] at h1
    exact ⟨h1.1, fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h1.2
      · exact h2 x hx⟩

theorem good_mkAppN {isAux : Name → Bool} : ∀ {f : Expr} {as : List Expr},
    Good ctx isAux (Expr.mkAppN f as) → Good ctx isAux f ∧ ∀ a ∈ as, Good ctx isAux a
  | _, [], h => ⟨h, fun _ ha => nomatch ha⟩
  | f, a :: as, h => by
    obtain ⟨h1, h2⟩ := good_mkAppN (f := .app f a) (as := as) h
    simp only [Good] at h1
    exact ⟨h1.1, fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h1.2
      · exact h2 x hx⟩

theorem fvarB_le_of_wscoped : ∀ {e : Expr} {d : Nat}, Expr.WScoped d e → e.fvarB ≤ d := by
  intro e d h
  rw [Expr.fvarB_eq, ← Expr.fvarsBelow_iff]
  induction e generalizing d with
  | fvar i ty _ => simp only [Expr.WScoped] at h; exact h.1
  | app f a ihf iha => simp only [Expr.WScoped] at h; exact ⟨ihf h.1, iha h.2⟩
  | lam t b m iht ihb | forallE t b m iht ihb =>
    simp only [Expr.WScoped] at h; exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb => simp only [Expr.WScoped] at h; exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i e ih => simp only [Expr.WScoped] at h; exact ih h
  | _ => trivial

/-- `is_nested_inductive_app`'s positive answer, inverted. -/
theorem isNestedApp_inv {c : Official.ElimCtx} {mem : List Name} {e : Expr} {I : Name}
    {us : List Level} {np : Nat} {args : List Expr}
    (h : Official.isNestedApp c mem e = .ok (some (I, us, np, args))) :
    e.getAppFn = .const I us ∧ e.getAppArgs = args ∧ I ≠ quotName ∧
      (∃ cv caps, c.find? I = some (.indInfo cv caps) ∧ caps.nparams = np) ∧
      np ≤ args.length ∧ (args.take np).any (·.nestOcc mem 0 0) = true ∧
      ∀ d ∈ args.take np, d.bvarB = 0 := by
  unfold Official.isNestedApp at h
  split at h
  · split at h
    · rename_i I' us' hfn
      split at h
      · rename_i cv caps hf
        split at h
        · simp [pure, Except.pure] at h
        · rename_i hq
          simp only at h
          split at h
          · simp [pure, Except.pure] at h
          · rename_i hlen
            split at h
            · simp [pure, Except.pure] at h
            · rename_i hocc
              split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · rename_i hbv
                simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                refine ⟨hfn, rfl, by simpa using hq, ⟨cv, caps, hf, rfl⟩, by omega,
                  by simpa using hocc, fun d hd => ?_⟩
                simp only [List.any_eq_true, bne_iff_ne, ne_eq, not_exists, not_and,
                  Decidable.not_not] at hbv
                exact hbv d hd
      · simp [pure, Except.pure] at h
    · simp [pure, Except.pure] at h
  · simp [pure, Except.pure] at h

/-- **THE ROOT RELATION.**  Official's replacement (against its final
auxiliary map) of a walk-shaped term is `SRel`-related to the term's
member abstraction at the empty frame stack: every replaced occurrence
is a fresh container instantiation whose read-back key is `M`'s. -/
theorem srel_sigma (hh : HolesOk ctx holes) (hlv : σ.lvls = ctx.lps.map .param)
    {c : Official.ElimCtx} {M : List (Expr × Name)}
    (hclv : c.lvls = σ.lvls) (hcps : c.ps = σ.ps)
    (hcont : ∀ K, σ.contAux K = M.lookup (rbExpr ctx K))
    (hind : ∀ I cv caps, c.find? I = some (.indInfo cv caps) → ctx.names.contains I = false) :
    ∀ (u : Expr), SigOk c ctx.names M u → Good ctx σ.isAux u →
      Expr.WScoped (ctx.hiAt 0) (nestAbstract ctx holes u) →
      SRel ctx σ [] [] (nestAbstract ctx holes u) (sigmaAll c ctx.names M u) := by
  intro u
  induction u with
  | app f a ihf iha =>
    intro hsig hg hws
    cases hN : Official.isNestedApp c ctx.names (.app f a) with
    | error e =>
      simp only [SigOk, hN] at hsig
    | ok r =>
      cases r with
      | none =>
        simp only [SigOk, hN] at hsig
        simp only [Good] at hg
        rw [abs_app] at hws ⊢
        simp only [Expr.WScoped] at hws
        simp only [sigmaAll, hN]
        exact .app (ihf hsig.1 hg.1 hws.1) (iha hsig.2 hg.2 hws.2)
      | some q =>
        obtain ⟨I, us, np, args⟩ := q
        simp only [SigOk, hN] at hsig
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsig
        obtain ⟨hfn, hargs, hquot, ⟨cv, caps, hfind, -⟩, hnp, hocc, hbv⟩ := isNestedApp_inv hN
        have hu : Expr.app f a = Expr.mkAppN (.const I us) args := by
          rw [← hfn, ← hargs, Expr.mkAppN_getApp]
        have hI := hind I cv caps hfind
        simp only [sigmaAll, hN, hx]
        rw [hu] at hg hws ⊢
        have habsI : nestAbstract ctx holes (.const I us) = .const I us := by
          rcases nestAbstract_const hh I us with ⟨m, ty, hc, -⟩ | ⟨-, h⟩
          · rw [hI] at hc; exact nomatch hc
          · exact h
        rw [abs_mkAppN, habsI] at hws ⊢
        obtain ⟨-, hgargs⟩ := good_mkAppN hg
        obtain ⟨-, hwargs⟩ := wscoped_mkAppN hws
        have hsplit : args.map (nestAbstract ctx holes) =
            (args.take np).map (nestAbstract ctx holes) ++
              (args.drop np).map (nestAbstract ctx holes) := by
          rw [← List.map_append, List.take_append_drop]
        rw [hsplit, mkAppN_append]
        have h3 : ∀ y ∈ (args.take np).map (nestAbstract ctx holes),
            y.bvarB = 0 ∧ y.fvarB ≤ ctx.hiAt ([] : List NestHole).length := by
          intro y hy
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
          refine ⟨?_, fvarB_le_of_wscoped (hwargs _ (List.mem_map_of_mem
            (List.mem_of_mem_take hd)))⟩
          have hb := hbv d hd
          have hl : (nestAbstract ctx holes d).looseBVarsBounded 0 = true := by
            refine looseBVarsBounded_replaceConsts (fun c' us' r hr => ?_) d 0 ?_
            · split at hr
              · split at hr
                · rename_i mm hmm
                  obtain ⟨hm, -⟩ := findIdx?_spec hmm
                  obtain ⟨ty, hty, -, hbty⟩ := hh mm hm
                  rw [hty] at hr
                  cases hr
                  simp [Expr.looseBVarsBounded]
                · exact nomatch hr
              · exact nomatch hr
            · exact Expr.bvarB_le (by omega)
          have := Expr.looseBVarsBounded_iff.mp hl
          rw [Expr.bvarB_eq]; omega
        have h4 : ∀ y ∈ (args.take np).map (nestAbstract ctx holes),
            Expr.WScoped (ctx.hiAt ([] : List NestHole).length) y := by
          intro y hy
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
          exact hwargs _ (List.mem_map_of_mem (List.mem_of_mem_take hd))
        have h5 : ∃ y ∈ (args.take np).map (nestAbstract ctx holes),
            y.nestOcc ctx.names ctx.nP (ctx.hiAt ([] : List NestHole).length) = true := by
          obtain ⟨d, hd, hdo⟩ := List.any_eq_true.mp hocc
          exact ⟨_, List.mem_map_of_mem hd,
            nestOcc_abs hh d (hgargs d (List.mem_of_mem_take hd)) hdo⟩
        have hk : ContKeyOk ctx [] [] I us ((args.take np).map (nestAbstract ctx holes)) :=
          ⟨hI, hquot, h3, h4, h5, by simp, by simp⟩
        refine SRel.mkAppN ?_ ?_
        · rw [hclv, hcps]
          refine .cnt ?_ hk
          rw [hcont]
          simp only [rbExpr, List.map_map]
          have : (args.take np).map ((·.replaceFVars (nestHoleConst ctx [])) ∘
              nestAbstract ctx holes) = args.take np := by
            conv => rhs; rw [← List.map_id (args.take np)]
            refine List.map_congr_left (fun d hd => ?_)
            exact rb_abs hh d (hgargs d (List.mem_of_mem_take hd))
          rw [this, hx]
        · have : ∀ (xs : List Expr), (∀ d ∈ xs, Good ctx σ.isAux d) →
              Rel2 (SRel ctx σ [] []) (xs.map (nestAbstract ctx holes)) xs := by
            intro xs hxs
            induction xs with
            | nil => exact .nil
            | cons d ds ih =>
              exact .cons (srel_abs_self hh hlv d (hxs d List.mem_cons_self))
                (ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy)))
          exact this _ (fun d hd => hgargs d (List.mem_of_mem_drop hd))
  | lam t b m iht ihb =>
    intro hsig hg hws
    simp only [SigOk] at hsig; simp only [Good] at hg
    rw [abs_lam] at hws ⊢; simp only [Expr.WScoped] at hws
    exact .lam (iht hsig.1 hg.1 hws.1) (ihb hsig.2 hg.2 hws.2)
  | forallE t b m iht ihb =>
    intro hsig hg hws
    simp only [SigOk] at hsig; simp only [Good] at hg
    rw [abs_forallE] at hws ⊢; simp only [Expr.WScoped] at hws
    exact .forallE (iht hsig.1 hg.1 hws.1) (ihb hsig.2 hg.2 hws.2)
  | letE t v b iht ihv ihb =>
    intro hsig hg hws
    simp only [SigOk] at hsig; simp only [Good] at hg
    rw [abs_letE] at hws ⊢; simp only [Expr.WScoped] at hws
    exact .letE (iht hsig.1 hg.1 hws.1) (ihv hsig.2.1 hg.2.1 hws.2.1) (ihb hsig.2.2 hg.2.2 hws.2.2)
  | proj s i e ih =>
    intro hsig hg hws
    simp only [SigOk] at hsig; simp only [Good] at hg
    rw [abs_proj] at hws ⊢; simp only [Expr.WScoped] at hws
    exact .proj (ih hsig hg hws)
  | const n us => intro _ hg _; exact srel_abs_self hh hlv _ hg
  | fvar i ty _ => intro _ hg _; exact srel_abs_self hh hlv _ hg
  | bvar i => intro _ _ _; exact .bvar i
  | sort u => intro _ _ _; exact .sort u
  | lit l => intro _ _ _; exact .lit l

/-- The abstraction commutes with instantiation (the holes are closed). -/
theorem abs_instantiate1 (hh : HolesOk ctx holes) {v : Expr} :
    ∀ (e : Expr) (k : Nat), nestAbstract ctx holes (e.instantiate1 v k) =
      (nestAbstract ctx holes e).instantiate1 (nestAbstract ctx holes v) k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    show nestAbstract ctx holes ((Expr.bvar i).instantiate1 v k) =
      (Expr.bvar i).instantiate1 (nestAbstract ctx holes v) k
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | const n us =>
    intro k
    rcases nestAbstract_const hh n us with ⟨m, ty, -, -, -, -, -, hbv, h⟩ | ⟨-, h⟩
    · rw [show (Expr.const n us).instantiate1 v k = .const n us from rfl, h]
      simp only [Expr.instantiate1]
    · rw [show (Expr.const n us).instantiate1 v k = .const n us from rfl, h]; rfl
  | fvar i ty _ => intro k; rfl
  | app f a ihf iha => intro k; simp only [Expr.instantiate1, abs_app]; rw [ihf, iha]
  | lam t b m iht ihb => intro k; simp only [Expr.instantiate1, abs_lam]; rw [iht, ihb]
  | forallE t b m iht ihb => intro k; simp only [Expr.instantiate1, abs_forallE]; rw [iht, ihb]
  | letE t v' b iht ihv ihb =>
    intro k; simp only [Expr.instantiate1, abs_letE]; rw [iht, ihv, ihb]
  | proj s i e ih => intro k; simp only [Expr.instantiate1, abs_proj]; rw [ih]
  | sort u => intro k; rfl
  | lit l => intro k; rfl

/-- The walk's input shape survives instantiation at a well-shaped value. -/
theorem good_instantiate1 {isAux : Name → Bool} {v : Expr} (hv : Good ctx isAux v) :
    ∀ (e : Expr) (k : Nat), Good ctx isAux e → Good ctx isAux (e.instantiate1 v k) := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> trivial
  | app f a ihf iha => intro k h; simp only [Good] at h; exact ⟨ihf k h.1, iha k h.2⟩
  | lam t b m iht ihb => intro k h; simp only [Good] at h; exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE t b m iht ihb => intro k h; simp only [Good] at h; exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE t v' b iht ihv ihb =>
    intro k h; simp only [Good] at h; exact ⟨iht k h.1, ihv k h.2.1, ihb (k + 1) h.2.2⟩
  | proj s i e ih => intro k h; simp only [Good] at h; exact ih k h
  | _ => intro k h; exact h

/-- The parameters: canonical variables below `nP`, well shaped, fixed by
the abstraction and scoped. -/
@[expose] def ParamsOk (ctx : NestCtx) (isAux : Name → Bool) : Prop :=
  ∀ p ∈ ctx.params, Good ctx isAux p ∧
    p.deepOcc (fun n => ctx.names.contains n || isAux n) = false ∧ Expr.WScoped ctx.nP p

theorem instPisWith_facts (hh : HolesOk ctx holes) (hps : ParamsOk ctx σ.isAux) :
    ∀ (ps : List Expr), (∀ p ∈ ps, p ∈ ctx.params) → ∀ (t u : Expr),
      instPisWith ps t = some u → Good ctx σ.isAux t →
      Expr.WScoped (ctx.hiAt 0) (nestAbstract ctx holes t) →
      instPisWith ps (nestAbstract ctx holes t) = some (nestAbstract ctx holes u) ∧
        Good ctx σ.isAux u ∧ Expr.WScoped (ctx.hiAt 0) (nestAbstract ctx holes u)
  | [], _, t, u, h, hg, hw => by
    simp only [instPisWith, Option.some.injEq] at h
    subst h
    exact ⟨rfl, hg, hw⟩
  | p :: ps, hin, t, u, h, hg, hw => by
    cases t with
    | forallE a b m =>
      simp only [instPisWith] at h
      obtain ⟨hgp, hdp, hwp⟩ := hps p (hin p List.mem_cons_self)
      have habsp : nestAbstract ctx holes p = p :=
        nestAbstract_of_deepFree hh (fun n hn => by rw [hn, Bool.true_or]) p hdp
      simp only [Good] at hg
      rw [abs_forallE] at hw
      simp only [Expr.WScoped] at hw
      have hb' := instPisWith_facts hh hps ps (fun q hq => hin q (List.mem_cons_of_mem _ hq))
        (b.instantiate1 p) u h (good_instantiate1 hgp b 0 hg.2)
        (by rw [abs_instantiate1 hh, habsp]
            exact Expr.WScoped.instantiate1_gen
              (Expr.WScoped.mono (by simp [NestCtx.hiAt]) hwp) 0 hw.2)
      refine ⟨?_, hb'.2⟩
      rw [abs_forallE]
      simp only [instPisWith]
      rw [← habsp, ← abs_instantiate1 hh]
      exact hb'.1
    | _ => simp [instPisWith] at h

/-- **(A) AT THE ROOT**: a member constructor's walk input
(`instPisWith params (nestAbstract t)`) is `SRel`-related, at the empty
frame stack, to official's replaced constructor (`sigmaAll` of
`instantiate params t`). -/
theorem srel_member_root (hh : HolesOk ctx holes) (hlv : σ.lvls = ctx.lps.map .param)
    (hps : ParamsOk ctx σ.isAux)
    {c : Official.ElimCtx} {M : List (Expr × Name)}
    (hclv : c.lvls = σ.lvls) (hcps : c.ps = σ.ps)
    (hcont : ∀ K, σ.contAux K = M.lookup (rbExpr ctx K))
    (hind : ∀ I cv caps, c.find? I = some (.indInfo cv caps) → ctx.names.contains I = false)
    {t u : Expr} (hcl : t.hasFvar = false) (hgt : Good ctx σ.isAux t)
    (hu : instPisWith ctx.params t = some u) (hsig : SigOk c ctx.names M u) :
    ∃ crest, instPisWith ctx.params (nestAbstract ctx holes t) = some crest ∧
      SRel ctx σ [] [] crest (sigmaAll c ctx.names M u) := by
  have hwt : Expr.WScoped (ctx.hiAt 0) (nestAbstract ctx holes t) := by
    refine ConLeche.WScoped.replaceConsts_closed (fun c' us' r hr => ?_) t hcl
    split at hr
    · split at hr
      · rename_i mm hmm
        obtain ⟨hm, -⟩ := findIdx?_spec hmm
        obtain ⟨ty, hty, hcty, -⟩ := hh mm hm
        rw [hty] at hr
        cases hr
        simp only [Expr.WScoped, NestCtx.hiAt]
        exact ⟨by omega, Expr.WScoped.of_not_hasFvar hcty⟩
      · exact nomatch hr
    · exact nomatch hr
  obtain ⟨h1, h2, h3⟩ := instPisWith_facts hh hps ctx.params (fun p hp => hp) t u hu hgt hwt
  exact ⟨_, h1, srel_sigma hh hlv hclv hcps hcont hind u hsig h2 h3⟩

end Lemmas

/-- **(A) ∘ (B) FROM THE ROOT.**  A member constructor `t` (closed, its
members at the block's levels): if official's positivity check accepts
its replaced form (`sigmaAll` of `t` at the parameters, against the final
auxiliary map `M`), then — under `WhnfSim`, the two recursion obligations
(`ContProv`, `SynProv`) at the empty stack, and the non-positivity checks
(`hside`) — the walk's run of the member constructor succeeds once its
input-derived fuel reaches the derivation's index `n`. -/
theorem nestMemberCtor_of_official_root {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {σ : SigmaCtx} {o : Official.PosOracle} {holes : List Expr}
    (hσ : SigmaOk ctx σ o) (hsim : WhnfSim ops env ctx σ o.whnf)
    (hprov : ContProv ops env ctx σ o [] []) (hsyn : SynProv ops env ctx σ o [] [])
    (hh : HolesOk ctx holes) (hlv : σ.lvls = ctx.lps.map .param) (hps : ParamsOk ctx σ.isAux)
    {c : Official.ElimCtx} {M : List (Expr × Name)}
    (hclv : c.lvls = σ.lvls) (hcps : c.ps = σ.ps)
    (hcont : ∀ K, σ.contAux K = M.lookup (rbExpr ctx K))
    (hind : ∀ I cv caps, c.find? I = some (.indInfo cv caps) → ctx.names.contains I = false)
    {self : Name} (hself : ctx.names.contains self = true)
    {t u : Expr} (hcl : t.hasFvar = false) (hgt : Good ctx σ.isAux t)
    (hu : instPisWith ctx.params t = some u) (hsig : SigOk c ctx.names M u)
    {fuel nb nF : Nat}
    (hchk : Official.checkCtorPos o self fuel nb (ctx.hiAt 0) (sigmaAll c ctx.names M u) = .ok ())
    {crest : Expr} (hcrest : instPisWith ctx.params (nestAbstract ctx holes t) = some crest)
    (hpi : crest.piArity = nF)
    (hside : ∀ n ks nds cur, PosDR ops env ctx n (.tele [] [] (ctx.hiAt 0) nF 0 crest ks nds cur) →
      ((List.range nF).any fun i => (ks.getD i .ordinary).guarded &&
        structUsedLater (closeTelescope nds (ctx.hiAt 0) cur) 0 i) = false ∧
      (closeTelescope nds (ctx.hiAt 0) cur).holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true) :
    ∃ n, ∀ st, RInv ctx st [] → n ≤ whnfWalkFuel crest →
      ∃ ks tyN st', nestMemberCtor ops env ctx nF crest st = .ok (ks, tyN, st') := by
  obtain ⟨crest', h1, hrel⟩ := srel_member_root hh hlv hps hclv hcps hcont hind hcl hgt hu hsig
  rw [hcrest] at h1
  cases h1
  exact nestMemberCtor_of_official hσ hsim hprov hsyn hself hrel hpi hchk hside

end ConLeche
