module

public import ConLeche.Verify.Inductives.PosCompleteRun
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Shift

public section

/-!
# The frame-constructor relation (lane COMPLETE-3, (A))

Below a frame, the walk reads a container's constructor instantiated at
the frame's key, its group abstracted to the frame's holes; official
reads the auxiliary type's constructor — the container's constructor at
the key's READ-BACK (`rbE`: every hole back to its constant), after its
replacement (`sigmaAll`).  This module relates the two: a walk term of
the walk's shape (`WShape`: members and frames' groups only as holes, a
frame's hole always applied to its key's parameters) is `SRel`-related
to official's replacement of its read-back (`srel_rb`), and to its raw
read-back (`srel_raw`, for the positions official does not traverse).
-/

namespace ConLeche

open Expr

section Frame

variable {ctx : NestCtx} {σ : SigmaCtx}

theorem Rel2.of_map {α β : Type} {R : α → β → Prop} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, R x (g x)) → Rel2 R l (l.map g)
  | [], _ => .nil
  | x :: _, h => .cons (h x List.mem_cons_self)
      (Rel2.of_map fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem rbE_app (prog : List NestHole) (f a : Expr) :
    rbE ctx prog (.app f a) = .app (rbE ctx prog f) (rbE ctx prog a) := rfl
theorem rbE_lam (prog : List NestHole) (t b : Expr) (m : BinderMeta) :
    rbE ctx prog (.lam t b m) = .lam (rbE ctx prog t) (rbE ctx prog b) m := rfl
theorem rbE_forallE (prog : List NestHole) (t b : Expr) (m : BinderMeta) :
    rbE ctx prog (.forallE t b m) = .forallE (rbE ctx prog t) (rbE ctx prog b) m := rfl
theorem rbE_letE (prog : List NestHole) (t v b : Expr) :
    rbE ctx prog (.letE t v b) = .letE (rbE ctx prog t) (rbE ctx prog v) (rbE ctx prog b) := rfl
theorem rbE_proj (prog : List NestHole) (s : Name) (i : Nat) (x : Expr) :
    rbE ctx prog (.proj s i x) = .proj s i (rbE ctx prog x) := rfl

theorem rbE_mkAppN (prog : List NestHole) :
    ∀ (args : List Expr) (f : Expr),
      rbE ctx prog (Expr.mkAppN f args) = Expr.mkAppN (rbE ctx prog f) (args.map (rbE ctx prog))
  | [], _ => rfl
  | a :: as, f => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl, rbE_mkAppN prog as]
    rfl

theorem nestHoleConst_par {prog : List NestHole} {i : Nat} (hi : i < ctx.nP) :
    nestHoleConst ctx prog i = none := by
  unfold nestHoleConst
  have h1 : ¬(ctx.nP ≤ i ∧ i < ctx.hiAt 0) := by omega
  have h2 : ¬(ctx.hiAt 0 ≤ i ∧ i < ctx.hiAt prog.length) := by simp only [NestCtx.hiAt]; omega
  rw [if_neg h1, if_neg h2]

theorem nestHoleConst_mem {prog : List NestHole} {t : Nat} (ht : t < ctx.names.length) :
    nestHoleConst ctx prog (ctx.nP + t) =
      some (.const (ctx.names.getD t .anonymous) (ctx.lps.map .param)) := by
  unfold nestHoleConst
  have h1 : ctx.nP ≤ ctx.nP + t ∧ ctx.nP + t < ctx.hiAt 0 := by simp only [NestCtx.hiAt]; omega
  rw [if_pos h1]
  simp

theorem nestHoleConst_frm {prog : List NestHole} {i : Nat} {h : NestHole}
    (hk : prog.reverse[i]? = some h) :
    nestHoleConst ctx prog (ctx.hiAt 0 + i) = some (.const h.key.cname h.key.lvls) := by
  have hi : i < prog.length := by
    have := (List.getElem?_eq_some_iff.mp hk).1
    simpa using this
  unfold nestHoleConst
  have h1 : ¬(ctx.nP ≤ ctx.hiAt 0 + i ∧ ctx.hiAt 0 + i < ctx.hiAt 0) := by omega
  have h2 : ctx.hiAt 0 ≤ ctx.hiAt 0 + i ∧ ctx.hiAt 0 + i < ctx.hiAt prog.length := by
    simp only [NestCtx.hiAt]; omega
  rw [if_neg h1, if_pos h2]
  simp [hk]

theorem rbE_par {prog : List NestHole} {i : Nat} {ty : Expr} (hi : i < ctx.nP) :
    rbE ctx prog (.fvar i ty) = .fvar i ty := by
  simp only [rbE, Expr.replaceFVars, nestHoleConst_par hi]
  rfl

theorem rbE_mem {prog : List NestHole} {t : Nat} {ty : Expr} (ht : t < ctx.names.length) :
    rbE ctx prog (.fvar (ctx.nP + t) ty) =
      .const (ctx.names.getD t .anonymous) (ctx.lps.map .param) := by
  simp only [rbE, Expr.replaceFVars, nestHoleConst_mem ht]
  rfl

theorem rbE_frm {prog : List NestHole} {i : Nat} {ty : Expr} {h : NestHole}
    (hk : prog.reverse[i]? = some h) :
    rbE ctx prog (.fvar (ctx.hiAt 0 + i) ty) = .const h.key.cname h.key.lvls := by
  simp only [rbE, Expr.replaceFVars, nestHoleConst_frm hk]
  rfl

/-- The read-back keeps the loose bound variables (it replaces free
variables by constants). -/
theorem rbE_lbb (prog : List NestHole) :
    ∀ (x : Expr) (k : Nat), (rbE ctx prog x).looseBVarsBounded k = x.looseBVarsBounded k := by
  intro x
  induction x with
  | fvar i ty _ =>
    intro k
    simp only [rbE, Expr.replaceFVars]
    cases hc : nestHoleConst ctx prog i with
    | none => rfl
    | some c =>
      unfold nestHoleConst at hc
      split at hc
      · cases hc; rfl
      · split at hc
        · cases hr : prog.reverse[i - ctx.hiAt 0]? with
          | none => rw [hr] at hc; exact nomatch hc
          | some h => rw [hr] at hc; cases hc; rfl
        · exact nomatch hc
  | app f a ihf iha => intro k; simp only [rbE_app, Expr.looseBVarsBounded, ihf, iha]
  | lam t b m iht ihb => intro k; simp only [rbE_lam, Expr.looseBVarsBounded, iht, ihb]
  | forallE t b m iht ihb => intro k; simp only [rbE_forallE, Expr.looseBVarsBounded, iht, ihb]
  | letE t v b iht ihv ihb => intro k; simp only [rbE_letE, Expr.looseBVarsBounded, iht, ihv, ihb]
  | proj s i x ih => intro k; simp only [rbE_proj, Expr.looseBVarsBounded, ih]
  | bvar i => intro k; rfl
  | sort u => intro k; rfl
  | const n us => intro k; rfl
  | lit l => intro k; rfl

/-- **The walk's shape under the frames `prog`**: no member and no
auxiliary constant (the members are holes), every free variable a
parameter (with a well-shaped annotation free of declared types), a
member hole, or a frame's hole applied to its key's parameters (then to
further well-shaped arguments). -/
inductive WShape (ctx : NestCtx) (isAux : Name → Bool) (prog : List NestHole) : Expr → Prop where
  | const {n : Name} {us : List Level} (hn : ctx.names.contains n = false) (ha : isAux n = false) :
      WShape ctx isAux prog (.const n us)
  | par {i : Nat} {ty : Expr} (hi : i < ctx.nP) (hg : Good ctx isAux ty)
      (hty : ty.deepOcc (fun n => ctx.names.contains n || isAux n) = false) :
      WShape ctx isAux prog (.fvar i ty)
  | mem {t : Nat} {ty : Expr} (ht : t < ctx.names.length) :
      WShape ctx isAux prog (.fvar (ctx.nP + t) ty)
  | frm {i : Nat} {ty : Expr} {h : NestHole} {is : List Expr} (hk : prog.reverse[i]? = some h)
      (his : ∀ x ∈ is, WShape ctx isAux prog x) :
      WShape ctx isAux prog (Expr.mkAppN (Expr.mkAppN (.fvar (ctx.hiAt 0 + i) ty) h.key.ds) is)
  | app {f a : Expr} (hnf : ∀ i ty, (Expr.app f a).getAppFn = .fvar i ty → i < ctx.hiAt 0)
      (hf : WShape ctx isAux prog f) (ha : WShape ctx isAux prog a) :
      WShape ctx isAux prog (.app f a)
  | lam {t b : Expr} {m : BinderMeta} : WShape ctx isAux prog t → WShape ctx isAux prog b →
      WShape ctx isAux prog (.lam t b m)
  | forallE {t b : Expr} {m : BinderMeta} : WShape ctx isAux prog t → WShape ctx isAux prog b →
      WShape ctx isAux prog (.forallE t b m)
  | letE {t v b : Expr} : WShape ctx isAux prog t → WShape ctx isAux prog v →
      WShape ctx isAux prog b → WShape ctx isAux prog (.letE t v b)
  | proj {s : Name} {i : Nat} {x : Expr} : WShape ctx isAux prog x →
      WShape ctx isAux prog (.proj s i x)
  | bvar (i : Nat) : WShape ctx isAux prog (.bvar i)
  | sort (u : Level) : WShape ctx isAux prog (.sort u)
  | lit (l : Literal) : WShape ctx isAux prog (.lit l)

/-- **The frames' keys read back are official's keys**: closed, mentioning
a member, headed by a stored inductive that is neither a member nor an
auxiliary type. -/
@[expose] def StackOk (ctx : NestCtx) (σ : SigmaCtx) (prog : List NestHole) : Prop :=
  ∀ (i : Nat) (h : NestHole), prog.reverse[i]? = some h →
    (∀ x ∈ h.key.ds, x.looseBVarsBounded 0 = true) ∧
    (rbKey ctx prog h.key).looseBVarsBounded 0 = true ∧
    (rbKey ctx prog h.key).nestOcc ctx.names 0 0 = true ∧
    ctx.names.contains h.key.cname = false ∧ σ.isAux h.key.cname = false

/-- **The raw relation**: a walk-shaped term is related to its raw
read-back (no replacement: a frame's hole application to its key). -/
theorem srel_raw (hlv : σ.lvls = ctx.lps.map .param) {prog : List NestHole}
    {act : List NestKey} (hso : StackOk ctx σ prog) :
    ∀ {x : Expr}, WShape ctx σ.isAux prog x → SRel ctx σ prog act x (rbE ctx prog x) := by
  intro x hx
  induction hx with
  | const hn ha => exact .const hn ha
  | @par i ty hi hg hty =>
    rw [rbE_par hi]
    exact .fvar (Or.inl hi) (srel_refl_deepFree ty hg hty)
  | @mem t ty ht =>
    rw [rbE_mem ht, ← hlv]
    exact .mem ht
  | @frm i ty h is hk _ ih =>
    obtain ⟨hcl, hrcl, hocc, hnm, hna⟩ := hso i h hk
    rw [rbE_mkAppN, rbE_mkAppN, rbE_frm hk]
    exact SRel.mkAppN (.raw hk hcl hrcl hocc hnm hna) (Rel2.of_map ih)
  | app _ _ _ ihf iha => exact .app ihf iha
  | lam _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ iht ihb => exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ih => exact .proj ih
  | bvar i => exact .bvar i
  | sort u => exact .sort u
  | lit l => exact .lit l

/-- `is_nested_inductive_app`'s positive answer, from its conditions. -/
theorem isNestedApp_of {c : Official.ElimCtx} {mem : List Name} {f a : Expr} {I : Name}
    {us : List Level} {cv : ConstantVal} {caps : IndCaps}
    (hfn : (Expr.app f a).getAppFn = .const I us) (hf : c.find? I = some (.indInfo cv caps))
    (hq : I ≠ quotName) (hle : caps.nparams ≤ (Expr.app f a).getAppArgs.length)
    (hocc : ((Expr.app f a).getAppArgs.take caps.nparams).any (·.nestOcc mem 0 0) = true)
    (hbv : ∀ d ∈ (Expr.app f a).getAppArgs.take caps.nparams, d.bvarB = 0) :
    Official.isNestedApp c mem (.app f a) =
      .ok (some (I, us, caps.nparams, (Expr.app f a).getAppArgs)) := by
  unfold Official.isNestedApp
  rw [hfn]
  dsimp only
  rw [hf]
  dsimp only
  rw [if_neg (by simpa using hq)]
  rw [if_neg (by omega)]
  rw [if_neg (by simp [hocc])]
  rw [if_neg (by
    simp only [List.any_eq_true, bne_iff_ne, ne_eq, not_exists, not_and, Decidable.not_not]
    exact hbv)]
  rfl

/-- A read-back occurrence of a member is a walk occurrence. -/
theorem nestOcc_of_rbE {prog : List NestHole} :
    ∀ {x : Expr}, WShape ctx σ.isAux prog x → (rbE ctx prog x).nestOcc ctx.names 0 0 = true →
      x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true := by
  intro x hx
  induction hx with
  | const hn _ =>
    intro h
    simp only [rbE, Expr.replaceFVars, Expr.nestOcc] at h
    rw [hn] at h; exact nomatch h
  | par hi _ _ => intro h; rw [rbE_par hi] at h; simp [Expr.nestOcc] at h
  | @mem t ty ht =>
    intro _
    simp [Expr.nestOcc, NestCtx.hiAt]
    omega
  | @frm i ty h is hk _ _ =>
    intro _
    have hi : i < prog.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      simpa using this
    simp only [nestOcc_mkAppN, Expr.nestOcc, NestCtx.hiAt, Bool.or_eq_true, decide_eq_true_eq]
    left; left; omega
  | app _ _ _ ihf iha =>
    simp only [rbE_app, Expr.nestOcc, Bool.or_eq_true]
    rintro (h | h)
    · exact .inl (ihf h)
    · exact .inr (iha h)
  | lam _ _ iht ihb | forallE _ _ iht ihb =>
    simp only [rbE_lam, rbE_forallE, Expr.nestOcc, Bool.or_eq_true]
    rintro (h | h)
    · exact .inl (iht h)
    · exact .inr (ihb h)
  | letE _ _ _ iht ihv ihb =>
    simp only [rbE_letE, Expr.nestOcc, Bool.or_eq_true]
    rintro ((h | h) | h)
    · exact .inl (.inl (iht h))
    · exact .inl (.inr (ihv h))
    · exact .inr (ihb h)
  | proj _ ih => simpa [rbE_proj, Expr.nestOcc] using ih
  | bvar i => intro h; simp [rbE, Expr.replaceFVars, Expr.nestOcc] at h
  | sort u => intro h; simp [rbE, Expr.replaceFVars, Expr.nestOcc] at h
  | lit l => intro h; simp [rbE, Expr.replaceFVars, Expr.nestOcc] at h

/-- The arguments of a walk-shaped application headed by a constant are
walk-shaped. -/
theorem WShape.args_of_const {prog : List NestHole} :
    ∀ {x : Expr}, WShape ctx σ.isAux prog x → ∀ {n : Name} {us : List Level},
      x.getAppFn = .const n us → ∀ y ∈ x.getAppArgs, WShape ctx σ.isAux prog y := by
  intro x hx
  induction hx with
  | frm hk _ _ =>
    intro n us hfn
    rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN] at hfn
    simp [Expr.getAppFn] at hfn
  | app _ _ ha ihf _ =>
    intro n us hfn y hy
    simp only [Expr.getAppFn] at hfn
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact ihf hfn y hy
    · exact ha
  | _ => intro n us hfn y hy; simp [Expr.getAppArgs] at hy

/-- **The official side of a frame stack**: every frame's container is a
stored inductive (official's `find`) at its recorded parameter count,
not `Quot`. -/
@[expose] def StackOff (c : Official.ElimCtx) (prog : List NestHole) : Prop :=
  ∀ (i : Nat) (h : NestHole), prog.reverse[i]? = some h →
    h.key.cname ≠ quotName ∧
    ∃ cv caps, c.find? h.key.cname = some (.indInfo cv caps) ∧ caps.nparams = h.key.ds.length

/-- **Every syntactic nested occurrence of `x` is fresh** (not a frame's
key, not in progress). -/
@[expose] def FreshOccs (ctx : NestCtx) (prog : List NestHole) (act : List NestKey) (x : Expr) :
    Prop :=
  ∀ s K, Expr.SubOf s x → nestSynApp? ctx (ctx.hiAt prog.length) s = some K →
    (∀ h ∈ prog, h.key ≠ K) ∧ K ∉ act

theorem wscoped_getAppArgs {d : Nat} {x : Expr} (h : Expr.WScoped d x) :
    ∀ y ∈ x.getAppArgs, Expr.WScoped d y := by
  rw [← Expr.mkAppN_getApp x] at h
  exact (wscoped_mkAppN h).2

theorem bvarB_zero_of_lbb {y : Expr} (h : y.looseBVarsBounded 0 = true) : y.bvarB = 0 := by
  have := Expr.looseBVarsBounded_iff.mp h
  rw [Expr.bvarB_eq]; omega

theorem lbb_mkAppN {k : Nat} : ∀ {f : Expr} {args : List Expr},
    (Expr.mkAppN f args).looseBVarsBounded k = true → ∀ d ∈ args, d.looseBVarsBounded k = true
  | _, [], _, _, hd => nomatch hd
  | f, a :: as, h, d, hd => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl] at h
    rcases List.mem_cons.mp hd with rfl | hd
    · have := lbb_mkAppN_head h
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at this
      exact this.2
    · exact lbb_mkAppN h d hd
where
  lbb_mkAppN_head : ∀ {f : Expr} {args : List Expr},
      (Expr.mkAppN f args).looseBVarsBounded k = true → f.looseBVarsBounded k = true
    | _, [], h => h
    | f, a :: as, h => by
      rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl] at h
      have := lbb_mkAppN_head h
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at this
      exact this.1

theorem lbb_of_bvarB_zero {y : Expr} (h : y.bvarB = 0) : y.looseBVarsBounded 0 = true :=
  Expr.looseBVarsBounded_iff.mpr (by simp [← Expr.bvarB_eq, h])

/-- **THE FRAME-CONSTRUCTOR RELATION.**  A walk-shaped term whose read-back
official's replacement accepts (`SigOk` against the final auxiliary map
`M`), every syntactic occurrence fresh, is `SRel`-related to official's
replacement of its read-back — when the σ-maps are `M` at the read-back
keys. -/
theorem srel_rb (hlv : σ.lvls = ctx.lps.map .param) {prog : List NestHole} {act : List NestKey}
    (hso : StackOk ctx σ prog) {c : Official.ElimCtx} {M : List (Expr × Name)}
    (hclv : c.lvls = σ.lvls) (hcps : c.ps = σ.ps)
    (hcont : ∀ K, σ.contAux prog K = M.lookup (rbKey ctx prog K))
    (hframe : ∀ (i : Nat) (h : NestHole), prog.reverse[i]? = some h →
      σ.frameAux prog h = M.lookup (rbKey ctx prog h.key))
    (hsoff : StackOff c prog)
    (hind : ∀ I cv caps, c.find? I = some (.indInfo cv caps) → ctx.names.contains I = false)
    (hfind : ∀ n, ctx.names.contains n = false → c.find? n = ctx.find? n) :
    ∀ {x : Expr}, WShape ctx σ.isAux prog x → Expr.WScoped (ctx.hiAt prog.length) x →
      SigOk c ctx.names M (rbE ctx prog x) → FreshOccs ctx prog act x →
      SRel ctx σ prog act x (sigmaAll c ctx.names M (rbE ctx prog x)) := by
  intro x hx
  induction hx with
  | const hn ha => intro _ _ _; exact .const hn ha
  | @par i ty hi hg hty =>
    intro _ _ _
    rw [rbE_par hi]
    exact .fvar (Or.inl hi) (srel_refl_deepFree ty hg hty)
  | @mem t ty ht =>
    intro _ _ _
    rw [rbE_mem ht]
    show SRel ctx σ prog act _ (.const _ _)
    rw [← hlv]
    exact .mem ht
  | @frm i ty h is hk his _ =>
    intro hws hsig _
    obtain ⟨hcl, hrcl, hocc, hnm, hna⟩ := hso i h hk
    obtain ⟨hq, cv, caps, hf, hnp⟩ := hsoff i h hk
    have hDs : (h.key.ds.map (rbE ctx prog)).any (·.nestOcc ctx.names 0 0) = true := by
      simp only [rbKey, nestOcc_mkAppN, Expr.nestOcc, hnm, Bool.false_or] at hocc
      exact hocc
    obtain ⟨L, z, hLz⟩ : ∃ L z, h.key.ds.map (rbE ctx prog) ++ is.map (rbE ctx prog) = L ++ [z] := by
      rcases List.eq_nil_or_concat (h.key.ds.map (rbE ctx prog) ++ is.map (rbE ctx prog)) with
        he | ⟨L, z, he⟩
      · rw [List.append_eq_nil_iff] at he
        rw [he.1] at hDs; simp at hDs
      · exact ⟨L, z, by rw [he, List.concat_eq_append]⟩
    have hre : rbE ctx prog (Expr.mkAppN (Expr.mkAppN (.fvar (ctx.hiAt 0 + i) ty) h.key.ds) is) =
        .app (Expr.mkAppN (.const h.key.cname h.key.lvls) L) z := by
      rw [rbE_mkAppN, rbE_mkAppN, rbE_frm hk, ← mkAppN_append, hLz, Expr.mkAppN_append_one]
    have hargs : (Expr.app (Expr.mkAppN (.const h.key.cname h.key.lvls) L) z).getAppArgs =
        h.key.ds.map (rbE ctx prog) ++ is.map (rbE ctx prog) := by
      rw [hLz]; simp [Expr.getAppArgs, Expr.getAppArgs_mkAppN]
    have htake : (h.key.ds.map (rbE ctx prog) ++ is.map (rbE ctx prog)).take caps.nparams =
        h.key.ds.map (rbE ctx prog) := by
      rw [hnp]; simp
    have hN := isNestedApp_of (c := c) (mem := ctx.names) (cv := cv) (caps := caps)
      (f := Expr.mkAppN (.const h.key.cname h.key.lvls) L) (a := z)
      (by simp only [Expr.getAppFn]; rw [Expr.getAppFn_mkAppN]; rfl) hf hq
      (by rw [hargs, hnp]; simp)
      (by rw [hargs, htake]; exact hDs)
      (by
        rw [hargs, htake]
        intro d hd
        simp only [rbKey] at hrcl
        exact bvarB_zero_of_lbb (lbb_mkAppN hrcl d hd))
    rw [hre] at hsig ⊢
    have hlook : M.lookup (Expr.mkAppN (.const h.key.cname h.key.lvls)
        ((Expr.app (Expr.mkAppN (.const h.key.cname h.key.lvls) L) z).getAppArgs.take caps.nparams))
        = σ.frameAux prog h := by
      rw [hframe i h hk, hargs, htake]; rfl
    simp only [SigOk, hN] at hsig
    rw [hlook] at hsig
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsig
    simp only [sigmaAll, hN]
    rw [hlook, ha]
    simp only
    rw [hargs, hnp, List.drop_left' (by simp), hclv, hcps]
    exact SRel.mkAppN (.frm hk ha hcl) (Rel2.of_map fun y hy => srel_raw hlv hso (his y hy))
  | @app f a hnf hf ha ihf iha =>
    intro hws hsig hfr
    simp only [Expr.WScoped] at hws
    rw [rbE_app] at hsig ⊢
    cases hN : Official.isNestedApp c ctx.names (.app (rbE ctx prog f) (rbE ctx prog a)) with
    | error e => simp only [SigOk, hN] at hsig
    | ok r =>
      cases r with
      | none =>
        simp only [SigOk, hN] at hsig
        simp only [sigmaAll, hN]
        exact .app (ihf hws.1 hsig.1 fun s K hs hK => hfr s K (.appF _ hs) hK)
          (iha hws.2 hsig.2 fun s K hs hK => hfr s K (.appA _ hs) hK)
      | some q =>
        obtain ⟨I, us, np, args⟩ := q
        obtain ⟨hfn, hargs, hq, ⟨cv, caps, hfI, hnp⟩, hle, hocc, hbv⟩ := isNestedApp_inv hN
        have hI := hind I cv caps hfI
        subst hnp
        -- the walk's head is the container's constant
        have hsp := Expr.mkAppN_getApp (Expr.app f a)
        have hrsp : Expr.app (rbE ctx prog f) (rbE ctx prog a) =
            Expr.mkAppN (rbE ctx prog (Expr.app f a).getAppFn)
              ((Expr.app f a).getAppArgs.map (rbE ctx prog)) := by
          rw [← rbE_app, ← rbE_mkAppN, hsp]
        have hhd : (Expr.app f a).getAppFn = .const I us ∧
            args = (Expr.app f a).getAppArgs.map (rbE ctx prog) := by
          have hnotapp : ∀ f' a', (Expr.app f a).getAppFn ≠ .app f' a' := by
            intro f' a' he
            have : ∀ (e : Expr), ∀ f a, e.getAppFn ≠ .app f a := by
              intro e
              induction e with
              | app f a ihf _ => simpa [Expr.getAppFn] using ihf
              | _ => simp [Expr.getAppFn]
            exact this _ f' a' he
          generalize hg : (Expr.app f a).getAppFn = g at hnotapp hrsp hnf
          cases g with
          | const n us' =>
            rw [hrsp] at hfn hargs
            simp only [rbE, Expr.replaceFVars, Expr.getAppFn_mkAppN, Expr.getAppFn,
              Expr.const.injEq] at hfn
            obtain ⟨rfl, rfl⟩ := hfn
            refine ⟨rfl, ?_⟩
            rw [← hargs, Expr.getAppArgs_mkAppN]
            simp [rbE, Expr.replaceFVars, Expr.getAppArgs]
          | fvar i ty =>
            exfalso
            have hi := hnf i ty rfl
            by_cases hp : i < ctx.nP
            · rw [hrsp, rbE_par hp, Expr.getAppFn_mkAppN] at hfn
              simp [Expr.getAppFn] at hfn
            · obtain ⟨t, rfl⟩ : ∃ t, i = ctx.nP + t := ⟨i - ctx.nP, by omega⟩
              have ht : t < ctx.names.length := by simp [NestCtx.hiAt] at hi; omega
              rw [hrsp, rbE_mem ht, Expr.getAppFn_mkAppN] at hfn
              simp only [Expr.getAppFn, Expr.const.injEq] at hfn
              obtain ⟨rfl, -⟩ := hfn
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht] at hI
              simp [List.getElem_mem ht] at hI
          | app f' a' => exact absurd rfl (hnotapp f' a')
          | _ =>
            exfalso
            rw [hrsp, Expr.getAppFn_mkAppN] at hfn
            simp [rbE, Expr.replaceFVars, Expr.getAppFn] at hfn
        obtain ⟨hhead, hargs'⟩ := hhd
        have hxw₀ := (WShape.app hnf hf ha).args_of_const hhead
        have hxs₀ := wscoped_getAppArgs (x := .app f a) (by simp only [Expr.WScoped]; exact hws)
        obtain ⟨xargs, hxargs⟩ : ∃ xargs, (Expr.app f a).getAppArgs = xargs := ⟨_, rfl⟩
        rw [hxargs] at hargs' hxw₀ hxs₀
        have hxw : ∀ y ∈ xargs, WShape ctx σ.isAux prog y := hxw₀
        have hxs : ∀ y ∈ xargs, Expr.WScoped (ctx.hiAt prog.length) y := hxs₀
        -- the key and its auxiliary type
        have hkey : rbKey ctx prog ⟨I, us, xargs.take caps.nparams⟩ =
            Expr.mkAppN (.const I us) (args.take caps.nparams) := by
          simp only [rbKey, hargs', List.map_take]
        simp only [SigOk, hN] at hsig
        obtain ⟨aux, haux⟩ := Option.isSome_iff_exists.mp hsig
        have hca : σ.contAux prog ⟨I, us, xargs.take caps.nparams⟩ = some aux := by
          rw [hcont, hkey, haux]
        have hlenx : args.length = xargs.length := by rw [hargs']; simp
        have hwocc : ((xargs.take caps.nparams).any
            (·.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length))) = true := by
          rw [hargs', ← List.map_take, List.any_map] at hocc
          obtain ⟨y, hy, hyo⟩ := List.any_eq_true.mp hocc
          exact List.any_eq_true.mpr ⟨y, hy,
            nestOcc_of_rbE (hxw y (List.mem_of_mem_take hy)) hyo⟩
        have hsyn : nestSynApp? ctx (ctx.hiAt prog.length) (.app f a) =
            some ⟨I, us, xargs.take caps.nparams⟩ :=
          hxargs ▸ nestSynApp?_of hhead hI hq (by rw [← hfind I hI]; exact hfI)
            (by rw [hxargs]; omega) (by rw [hxargs]; exact hwocc)
        obtain ⟨hfp, hfa⟩ := hfr _ _ (.refl _) hsyn
        have hok : ContKeyOk ctx prog act I us (xargs.take caps.nparams) := by
          refine ⟨hI, hq, fun y hy => ⟨?_, fvarB_le_of_wscoped (hxs y (List.mem_of_mem_take hy))⟩,
            fun y hy => hxs y (List.mem_of_mem_take hy), ?_, hfp, hfa⟩
          · have hy' : rbE ctx prog y ∈ args.take caps.nparams := by
              rw [hargs', ← List.map_take]; exact List.mem_map_of_mem hy
            have := hbv _ hy'
            exact bvarB_zero_of_lbb (by rw [← rbE_lbb prog y 0]; exact lbb_of_bvarB_zero this)
          · obtain ⟨y, hy, hyo⟩ := List.any_eq_true.mp hwocc
            exact ⟨y, hy, hyo⟩
        simp only [sigmaAll, hN, haux]
        have hx : Expr.app f a = Expr.mkAppN (Expr.mkAppN (.const I us) (xargs.take caps.nparams))
            (xargs.drop caps.nparams) := by
          rw [← mkAppN_append, List.take_append_drop, ← hhead, ← hxargs, Expr.mkAppN_getApp]
        rw [hx, hclv, hcps]
        refine SRel.mkAppN (.cnt hca hok) ?_
        rw [hargs', ← List.map_drop]
        exact Rel2.of_map fun y hy => srel_raw hlv hso (hxw y (List.mem_of_mem_drop hy))
  | lam _ _ iht ihb =>
    intro hws hsig hfr
    simp only [Expr.WScoped] at hws
    rw [rbE_lam] at hsig ⊢
    simp only [SigOk] at hsig
    simp only [sigmaAll]
    exact .lam (iht hws.1 hsig.1 fun s K hs hK => hfr s K (.lamT _ _ hs) hK)
      (ihb hws.2 hsig.2 fun s K hs hK => hfr s K (.lamB _ _ hs) hK)
  | forallE _ _ iht ihb =>
    intro hws hsig hfr
    simp only [Expr.WScoped] at hws
    rw [rbE_forallE] at hsig ⊢
    simp only [SigOk] at hsig
    simp only [sigmaAll]
    exact .forallE (iht hws.1 hsig.1 fun s K hs hK => hfr s K (.piT _ _ hs) hK)
      (ihb hws.2 hsig.2 fun s K hs hK => hfr s K (.piB _ _ hs) hK)
  | letE _ _ _ iht ihv ihb =>
    intro hws hsig hfr
    simp only [Expr.WScoped] at hws
    rw [rbE_letE] at hsig ⊢
    simp only [SigOk] at hsig
    simp only [sigmaAll]
    exact .letE (iht hws.1 hsig.1 fun s K hs hK => hfr s K (.letT _ _ hs) hK)
      (ihv hws.2.1 hsig.2.1 fun s K hs hK => hfr s K (.letV _ _ hs) hK)
      (ihb hws.2.2 hsig.2.2 fun s K hs hK => hfr s K (.letB _ _ hs) hK)
  | proj _ ih =>
    intro hws hsig hfr
    simp only [Expr.WScoped] at hws
    rw [rbE_proj] at hsig ⊢
    simp only [SigOk] at hsig
    simp only [sigmaAll]
    exact .proj (ih hws hsig fun s K hs hK => hfr s K (.proj _ _ hs) hK)
  | bvar i => intro _ _ _; exact .bvar i
  | sort u => intro _ _ _; exact .sort u
  | lit l => intro _ _ _; exact .lit l

/-! ### Official's replacement is in normal form -/

/-- No auxiliary constant (official's input: a raw term). -/
@[expose] def NoAux (isAux : Name → Bool) : Expr → Prop
  | .const n _ => isAux n = false
  | .fvar _ _ | .bvar _ | .sort _ | .lit _ => True
  | .app f a => NoAux isAux f ∧ NoAux isAux a
  | .lam t b _ | .forallE t b _ => NoAux isAux t ∧ NoAux isAux b
  | .letE t v b => NoAux isAux t ∧ NoAux isAux v ∧ NoAux isAux b
  | .proj _ _ x => NoAux isAux x

theorem isNestedApp_ne_none {c : Official.ElimCtx} {mem : List Name} {f a : Expr} {I : Name}
    {us : List Level} {cv : ConstantVal} {caps : IndCaps}
    (hfn : (Expr.app f a).getAppFn = .const I us) (hf : c.find? I = some (.indInfo cv caps))
    (hq : I ≠ quotName) (hle : caps.nparams ≤ (Expr.app f a).getAppArgs.length)
    (hocc : ((Expr.app f a).getAppArgs.take caps.nparams).any (·.nestOcc mem 0 0) = true) :
    Official.isNestedApp c mem (.app f a) ≠ .ok none := by
  unfold Official.isNestedApp
  rw [hfn]
  dsimp only
  rw [hf]
  dsimp only
  rw [if_neg (by simpa using hq)]
  rw [if_neg (by omega)]
  rw [if_neg (by simp [hocc])]
  split
  · simp [throw, throwThe, MonadExceptOf.throw]
  · simp [pure, Except.pure]

section SigmaNF

variable {o : Official.PosOracle} {c : Official.ElimCtx} {M : List (Expr × Name)}

/-- The replacement's head: a σ-spine headed by a non-auxiliary constant was
not replaced anywhere along its spine. -/
theorem sigmaAll_spine (hMaux : ∀ k x, M.lookup k = some x → σ.isAux x = true) :
    ∀ (u : Expr) {C : Name} {us : List Level},
      (sigmaAll c ctx.names M u).getAppFn = .const C us → σ.isAux C = false →
      u.getAppFn = .const C us ∧
        (sigmaAll c ctx.names M u).getAppArgs = u.getAppArgs.map (sigmaAll c ctx.names M) := by
  intro u
  induction u with
  | app f a ihf _ =>
    intro C us hfn hC
    cases hN : Official.isNestedApp c ctx.names (.app f a) with
    | error e =>
      simp only [sigmaAll, hN, Expr.getAppFn] at hfn
      obtain ⟨h1, h2⟩ := ihf hfn hC
      refine ⟨by simpa [Expr.getAppFn] using h1, ?_⟩
      simp only [sigmaAll, hN, Expr.getAppArgs, h2, List.map_append, List.map_cons, List.map_nil]
    | ok r =>
      cases r with
      | none =>
        simp only [sigmaAll, hN, Expr.getAppFn] at hfn
        obtain ⟨h1, h2⟩ := ihf hfn hC
        refine ⟨by simpa [Expr.getAppFn] using h1, ?_⟩
        simp only [sigmaAll, hN, Expr.getAppArgs, h2, List.map_append, List.map_cons, List.map_nil]
      | some q =>
        obtain ⟨I, us', np, args⟩ := q
        simp only [sigmaAll, hN] at hfn
        split at hfn
        · rename_i x hx
          rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN] at hfn
          simp only [Expr.getAppFn, Expr.const.injEq] at hfn
          obtain ⟨rfl, -⟩ := hfn
          rw [hMaux _ _ hx] at hC; exact nomatch hC
        · simp only [Expr.getAppFn] at hfn
          obtain ⟨h1, h2⟩ := ihf hfn hC
          refine ⟨by simpa [Expr.getAppFn] using h1, ?_⟩
          rename_i hl
          simp only [sigmaAll, hN, hl, Expr.getAppArgs, h2, List.map_append, List.map_cons,
            List.map_nil]
  | const n us' =>
    intro C us hfn _
    simp only [sigmaAll, Expr.getAppFn] at hfn
    exact ⟨hfn, by simp [sigmaAll, Expr.getAppArgs]⟩
  | lam _ _ _ _ _ => intro C us hfn _; simp [sigmaAll, Expr.getAppFn] at hfn
  | forallE _ _ _ _ _ => intro C us hfn _; simp [sigmaAll, Expr.getAppFn] at hfn
  | letE _ _ _ _ _ _ => intro C us hfn _; simp [sigmaAll, Expr.getAppFn] at hfn
  | proj _ _ _ _ => intro C us hfn _; simp [sigmaAll, Expr.getAppFn] at hfn
  | bvar _ => intro C us hfn _; simp [sigmaAll, Expr.getAppFn] at hfn
  | fvar _ _ _ => intro C us hfn _; simp [sigmaAll, Expr.getAppFn] at hfn
  | sort _ => intro C us hfn _; simp [sigmaAll, Expr.getAppFn] at hfn
  | lit _ => intro C us hfn _; simp [sigmaAll, Expr.getAppFn] at hfn

/-- The replacement keeps the declared-type occurrences (a member stays, a
replaced occurrence mentions a member and becomes an auxiliary type). -/
theorem occ_sigmaAll (hσ : SigmaOk ctx σ o)
    (hMaux : ∀ k x, M.lookup k = some x → σ.isAux x = true) :
    ∀ (u : Expr), SigOk c ctx.names M u → NoAux σ.isAux u →
      o.occ (sigmaAll c ctx.names M u) = u.nestOcc ctx.names 0 0 := by
  intro u
  induction u with
  | app f a ihf iha =>
    intro hsig hna
    simp only [NoAux] at hna
    cases hN : Official.isNestedApp c ctx.names (.app f a) with
    | error e => simp only [SigOk, hN] at hsig
    | ok r =>
      cases r with
      | none =>
        simp only [SigOk, hN] at hsig
        simp only [sigmaAll, hN, Official.PosOracle.occ, Expr.nestOcc]
        rw [← Official.PosOracle.occ, ← Official.PosOracle.occ, ihf hsig.1 hna.1, iha hsig.2 hna.2]
      | some q =>
        obtain ⟨I, us, np, args⟩ := q
        simp only [SigOk, hN] at hsig
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsig
        obtain ⟨hfn, hargs, -, -, -, hocc, -⟩ := isNestedApp_inv hN
        simp only [sigmaAll, hN, hx]
        have h1 : o.occ (Expr.mkAppN (Expr.mkAppN (.const x c.lvls) c.ps) (args.drop np)) = true := by
          simp only [Official.PosOracle.occ, nestOcc_mkAppN, Expr.nestOcc, hσ.names, hMaux _ _ hx,
            Bool.or_true, Bool.true_or]
        rw [h1]
        symm
        rw [← Expr.mkAppN_getApp (.app f a), nestOcc_mkAppN, hargs]
        obtain ⟨y, hy, hyo⟩ := List.any_eq_true.mp hocc
        simp only [Bool.or_eq_true, List.any_eq_true]
        exact .inr ⟨y, List.mem_of_mem_take hy, hyo⟩
  | const n us =>
    intro _ hna
    simp only [NoAux] at hna
    simp only [sigmaAll, Official.PosOracle.occ, Expr.nestOcc]
    rw [hσ.names, hna, Bool.or_false]
  | lam t b m iht ihb | forallE t b m iht ihb =>
    intro hsig hna
    simp only [SigOk] at hsig; simp only [NoAux] at hna
    simp only [sigmaAll, Official.PosOracle.occ, Expr.nestOcc]
    rw [← Official.PosOracle.occ, ← Official.PosOracle.occ, iht hsig.1 hna.1, ihb hsig.2 hna.2]
  | letE t v b iht ihv ihb =>
    intro hsig hna
    simp only [SigOk] at hsig; simp only [NoAux] at hna
    simp only [sigmaAll, Official.PosOracle.occ, Expr.nestOcc]
    rw [← Official.PosOracle.occ, ← Official.PosOracle.occ, ← Official.PosOracle.occ,
      iht hsig.1 hna.1, ihv hsig.2.1 hna.2.1, ihb hsig.2.2 hna.2.2]
  | proj s i x ih =>
    intro hsig hna
    simp only [SigOk] at hsig; simp only [NoAux] at hna
    simp only [sigmaAll, Official.PosOracle.occ, Expr.nestOcc]
    rw [← Official.PosOracle.occ, ih hsig hna]
  | bvar _ => intro _ _; rfl
  | fvar _ _ _ => intro _ _; rfl
  | sort _ => intro _ _; rfl
  | lit _ => intro _ _; rfl

theorem noAux_args {isAux : Name → Bool} :
    ∀ {u : Expr}, NoAux isAux u → ∀ y ∈ u.getAppArgs, NoAux isAux y := by
  intro u
  induction u with
  | app f a ihf _ =>
    intro h y hy
    simp only [NoAux] at h
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact ihf h.1 y hy
    · exact h.2
  | _ => intro _ y hy; simp [Expr.getAppArgs] at hy

/-- A σ-occurrence of the replacement is a raw occurrence (a replaced
application mentions a member in its parameters). -/
theorem occ_sigmaAll_le (hσ : SigmaOk ctx σ o) :
    ∀ (u : Expr), NoAux σ.isAux u → o.occ (sigmaAll c ctx.names M u) = true →
      u.nestOcc ctx.names 0 0 = true := by
  intro u
  induction u with
  | app f a ihf iha =>
    intro hna h
    simp only [NoAux] at hna
    have hcong : o.occ (Expr.app (sigmaAll c ctx.names M f) (sigmaAll c ctx.names M a)) = true →
        (Expr.app f a).nestOcc ctx.names 0 0 = true := by
      intro h'
      simp only [Official.PosOracle.occ, Expr.nestOcc, Bool.or_eq_true] at h' ⊢
      rcases h' with h' | h'
      · exact .inl (ihf hna.1 h')
      · exact .inr (iha hna.2 h')
    cases hN : Official.isNestedApp c ctx.names (.app f a) with
    | error e => simp only [sigmaAll, hN] at h; exact hcong h
    | ok r =>
      cases r with
      | none => simp only [sigmaAll, hN] at h; exact hcong h
      | some q =>
        obtain ⟨I, us, np, args⟩ := q
        obtain ⟨-, hargs, -, -, -, hocc, -⟩ := isNestedApp_inv hN
        rw [← Expr.mkAppN_getApp (.app f a), nestOcc_mkAppN, hargs]
        obtain ⟨y, hy, hyo⟩ := List.any_eq_true.mp hocc
        simp only [Bool.or_eq_true, List.any_eq_true]
        exact .inr ⟨y, List.mem_of_mem_take hy, hyo⟩
  | const n us =>
    intro hna h
    simp only [NoAux] at hna
    simp only [sigmaAll, Official.PosOracle.occ, Expr.nestOcc] at h ⊢
    rw [hσ.names, hna, Bool.or_false] at h
    exact h
  | lam t b m iht ihb | forallE t b m iht ihb =>
    intro hna h
    simp only [NoAux] at hna
    simp only [sigmaAll, Official.PosOracle.occ, Expr.nestOcc, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact .inl (iht hna.1 h)
    · exact .inr (ihb hna.2 h)
  | letE t v b iht ihv ihb =>
    intro hna h
    simp only [NoAux] at hna
    simp only [sigmaAll, Official.PosOracle.occ, Expr.nestOcc, Bool.or_eq_true] at h ⊢
    rcases h with (h | h) | h
    · exact .inl (.inl (iht hna.1 h))
    · exact .inl (.inr (ihv hna.2.1 h))
    · exact .inr (ihb hna.2.2 h)
  | proj s i x ih =>
    intro hna h
    simp only [NoAux] at hna
    simp only [sigmaAll, Official.PosOracle.occ, Expr.nestOcc] at h ⊢
    exact ih hna h
  | bvar _ => intro _ h; simp [sigmaAll, Official.PosOracle.occ, Expr.nestOcc] at h
  | fvar _ _ _ => intro _ h; simp [sigmaAll, Official.PosOracle.occ, Expr.nestOcc] at h
  | sort _ => intro _ h; simp [sigmaAll, Official.PosOracle.occ, Expr.nestOcc] at h
  | lit _ => intro _ h; simp [sigmaAll, Official.PosOracle.occ, Expr.nestOcc] at h

/-- **Official's replacement is in normal form** (`SigNF`): every nested
application it traverses was replaced. -/
theorem sigmaAll_sigNF (hσ : SigmaOk ctx σ o) (hae : AuxEnvOk ctx σ)
    (hMaux : ∀ k x, M.lookup k = some x → σ.isAux x = true)
    (hfind : ∀ n, ctx.names.contains n = false → c.find? n = ctx.find? n) :
    ∀ (u : Expr), SigOk c ctx.names M u → NoAux σ.isAux u →
      SigNF ctx o σ.isAux (sigmaAll c ctx.names M u) := by
  intro u
  induction u with
  | app f a ihf iha =>
    intro hsig hna
    have hna' := hna
    simp only [NoAux] at hna
    cases hN : Official.isNestedApp c ctx.names (.app f a) with
    | error e => simp only [SigOk, hN] at hsig
    | ok r =>
      cases r with
      | some q =>
        obtain ⟨I, us, np, args⟩ := q
        simp only [SigOk, hN] at hsig
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsig
        simp only [sigmaAll, hN, hx]
        rw [← mkAppN_append]
        exact .aux (hMaux _ _ hx)
      | none =>
        simp only [SigOk, hN] at hsig
        simp only [sigmaAll, hN]
        refine .app ?_ (ihf hsig.1 hna.1) (iha hsig.2 hna.2)
        rintro ⟨C, us, caps, cv, hfn, hnm, hq, hf, hle, hany⟩
        have hC : σ.isAux C = false := by
          cases hc : σ.isAux C
          · rfl
          · exact absurd hf (hae.notStored C hc cv caps)
        have hsp := sigmaAll_spine (ctx := ctx) (σ := σ) (c := c) (M := M) hMaux (.app f a)
          (C := C) (us := us) (by simp only [sigmaAll, hN]; exact hfn) hC
        simp only [sigmaAll, hN] at hsp
        obtain ⟨hfn₀, hargs₀⟩ := hsp
        rw [hargs₀, ← List.map_take, List.any_map] at hany
        obtain ⟨y, hy, hyo⟩ := List.any_eq_true.mp hany
        have hyr := occ_sigmaAll_le hσ y
          (noAux_args hna' y (List.mem_of_mem_take hy)) hyo
        exact isNestedApp_ne_none hfn₀ (by rw [hfind C hnm]; exact hf) hq
          (by rw [hargs₀] at hle; simpa using hle)
          (List.any_eq_true.mpr ⟨y, hy, hyr⟩) hN
  | lam t b m iht ihb =>
    intro hsig hna
    simp only [SigOk] at hsig; simp only [NoAux] at hna
    exact .lam (iht hsig.1 hna.1) (ihb hsig.2 hna.2)
  | forallE t b m iht ihb =>
    intro hsig hna
    simp only [SigOk] at hsig; simp only [NoAux] at hna
    exact .forallE (iht hsig.1 hna.1) (ihb hsig.2 hna.2)
  | letE t v b iht ihv ihb =>
    intro hsig hna
    simp only [SigOk] at hsig; simp only [NoAux] at hna
    exact .letE (iht hsig.1 hna.1) (ihv hsig.2.1 hna.2.1) (ihb hsig.2.2 hna.2.2)
  | proj s i x ih =>
    intro hsig hna
    simp only [SigOk] at hsig; simp only [NoAux] at hna
    exact .proj (ih hsig hna)
  | bvar i => intro _ _; exact .bvar i
  | fvar i ty _ => intro _ _; exact .fvar i ty
  | sort u => intro _ _; exact .sort u
  | lit l => intro _ _; exact .lit l
  | const n us => intro _ _; exact .const n us

end SigmaNF

/-! ### A frame's constructor, read back -/

theorem rbE_instantiate1 {prog : List NestHole} {v : Expr} :
    ∀ (b : Expr) (k : Nat),
      rbE ctx prog (b.instantiate1 v k) = (rbE ctx prog b).instantiate1 (rbE ctx prog v) k := by
  have hb : ∀ j, rbE ctx prog (.bvar j) = .bvar j := fun _ => rfl
  intro b
  induction b with
  | bvar i =>
    intro k
    rw [hb]
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rw [hb]
  | fvar i ty _ =>
    intro k
    simp only [Expr.instantiate1, rbE, Expr.replaceFVars]
    cases hc : nestHoleConst ctx prog i with
    | none => rfl
    | some c =>
      unfold nestHoleConst at hc
      split at hc
      · cases hc; rfl
      · split at hc
        · cases hr : prog.reverse[i - ctx.hiAt 0]? with
          | none => rw [hr] at hc; exact nomatch hc
          | some h => rw [hr] at hc; cases hc; rfl
        · exact nomatch hc
  | app f a ihf iha => intro k; simp only [Expr.instantiate1, rbE_app, ihf, iha]
  | lam t b m iht ihb => intro k; simp only [Expr.instantiate1, rbE_lam, iht, ihb]
  | forallE t b m iht ihb => intro k; simp only [Expr.instantiate1, rbE_forallE, iht, ihb]
  | letE t v' b iht ihv ihb => intro k; simp only [Expr.instantiate1, rbE_letE, iht, ihv, ihb]
  | proj s i x ih => intro k; simp only [Expr.instantiate1, rbE_proj, ih]
  | sort u => intro k; rfl
  | const n us => intro k; rfl
  | lit l => intro k; rfl

/-- The read-back commutes with instantiating the parameters. -/
theorem rbE_instPisWith {prog : List NestHole} :
    ∀ (ds : List Expr) (t r : Expr), instPisWith ds t = some r →
      instPisWith (ds.map (rbE ctx prog)) (rbE ctx prog t) = some (rbE ctx prog r)
  | [], t, r, h => by simp only [instPisWith, Option.some.injEq] at h; subst h; rfl
  | d :: ds, t, r, h => by
    cases t with
    | forallE a b m =>
      simp only [instPisWith] at h
      simp only [List.map_cons, rbE_forallE, instPisWith]
      rw [← rbE_instantiate1]
      exact rbE_instPisWith ds _ r h
    | _ => simp [instPisWith] at h

/-- **A frame's substitution, read back, is the identity** on a closed
stored type: the group's holes read back to the group's constants at
the frame's levels. -/
theorem lookup_mem_name {l : List (Name × Expr)} {n : Name} {e : Expr} :
    l.lookup n = some e → ∃ i, ∃ hi : i < l.length, l[i].1 = n ∧ l[i].2 = e := by
  induction l with
  | nil => simp [List.lookup]
  | cons p l ih =>
    intro h
    obtain ⟨k, b⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq] at h
      exact ⟨0, by simp, by simpa using (beq_iff_eq.mp hb).symm, by simpa using h⟩
    · obtain ⟨i, hi, h1, h2⟩ := ih h
      exact ⟨i + 1, by simp; omega, by simpa using h1, by simpa using h2⟩

theorem rbE_replaceConsts_grp {wp : List NestHole} {us : List Level} {ds : List Expr}
    {grp : List (Name × Expr)} :
    ∀ (t : Expr), t.hasFvar = false →
      rbE ctx ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp)
        (t.replaceConsts (grpSub us (ctx.hiAt wp.length) grp)) = t := by
  intro t
  induction t with
  | const n us' =>
    intro _
    simp only [Expr.replaceConsts, grpSub]
    split
    · rename_i hus
      have hus' : us' = us := by simpa using hus
      subst hus'
      cases hl : (grp.mapIdx fun i (c, ty) => (c, Expr.fvar (ctx.hiAt wp.length + i) ty)).lookup n with
      | none => rfl
      | some e =>
        simp only [Option.getD_some]
        -- the looked-up hole is the group member's
        obtain ⟨i, hi, hgi, rfl⟩ : ∃ i, ∃ hi : i < grp.length, grp[i].1 = n ∧
            e = Expr.fvar (ctx.hiAt wp.length + i) grp[i].2 := by
          obtain ⟨i, hi, h1, h2⟩ := lookup_mem_name hl
          simp only [List.length_mapIdx] at hi
          simp only [List.getElem_mapIdx] at h1 h2
          exact ⟨i, hi, h1, h2.symm⟩
        have hk : ((grpNews us' ds (ctx.hiAt wp.length) grp).reverse ++ wp).reverse[wp.length + i]? =
            some { key := ⟨n, us', ds⟩, base := ctx.hiAt wp.length } := by
          rw [List.reverse_append, List.reverse_reverse, List.getElem?_append_right (by simp)]
          simp [grpNews, hi, hgi]
        rw [show ctx.hiAt wp.length + i = ctx.hiAt 0 + (wp.length + i) by
          simp [NestCtx.hiAt]; omega]
        rw [rbE_frm hk]
    · rfl
  | fvar i ty _ => intro h; simp [Expr.hasFvar] at h
  | app f a ihf iha =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, rbE_app, ihf h.1, iha h.2]
  | lam t b m iht ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, rbE_lam, iht h.1, ihb h.2]
  | forallE t b m iht ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, rbE_forallE, iht h.1, ihb h.2]
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, rbE_letE, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj s i x ih =>
    intro h
    simp only [Expr.hasFvar] at h
    simp only [Expr.replaceConsts, rbE_proj, ih h]
  | bvar i => intro _; rfl
  | sort u => intro _; rfl
  | lit l => intro _; rfl

/-- **A frame's constructor meets `CtorStep`** — its relational core
discharged by the frame-constructor relation: official's auxiliary
constructor is the container's constructor at the key's read-back
(`instPisWith (ds.map rbE) t`, official's `instantiate_pi_params`), after
its replacement; given the walk's shape (the container's own-block
occurrences uniform), freshness of its syntactic occurrences, official's
acceptance of the auxiliary constructor, and the checks that are not
positivity. -/
theorem ctorStep_of {ops : CheckerOps CheckM} {env : Env} {o : Official.PosOracle}
    (hσ : SigmaOk ctx σ o) (hae : AuxEnvOk ctx σ) (hlv : σ.lvls = ctx.lps.map .param)
    {wp : List NestHole} {act : List NestKey} {us : List Level} {ds : List Expr}
    {grp : List (Name × Expr)} {c : Official.ElimCtx} {M : List (Expr × Name)}
    (hso : StackOk ctx σ ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp))
    (hsoff : StackOff c ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp))
    (hclv : c.lvls = σ.lvls) (hcps : c.ps = σ.ps)
    (hcont : ∀ K, σ.contAux ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp) K =
      M.lookup (rbKey ctx ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp) K))
    (hframe : ∀ (i : Nat) (h : NestHole),
      ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp).reverse[i]? = some h →
      σ.frameAux ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp) h =
        M.lookup (rbKey ctx ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp) h.key))
    (hind : ∀ I cv caps, c.find? I = some (.indInfo cv caps) → ctx.names.contains I = false)
    (hfind : ∀ n, ctx.names.contains n = false → c.find? n = ctx.find? n)
    (hMaux : ∀ k x, M.lookup k = some x → σ.isAux x = true)
    {cv : ConstantVal} {nF : Nat} (hnd : Name.nodup cv.levelParams = true)
    (hcl : (cv.type.instantiateLevelParams cv.levelParams us).hasFvar = false)
    {crest u : Expr}
    (hcr : instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
      (grpSub us (ctx.hiAt wp.length) grp)) = some crest)
    (hu : instPisWith (ds.map (rbE ctx ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp)))
      (cv.type.instantiateLevelParams cv.levelParams us) = some u)
    (hws : WShape ctx σ.isAux ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp) crest)
    (hsc : Expr.WScoped (ctx.hiAt ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp).length)
      crest)
    (hfr : FreshOccs ctx ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp)
      (grpKeys us ds grp ++ act) crest)
    (hpi : nF ≤ crest.piArity)
    (hoff : SigOk c ctx.names M u ∧ NoAux σ.isAux u ∧ ∃ self fuelO nb,
      Official.checkCtorPos o self fuelO nb
        (ctx.hiAt ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp).length)
        (sigmaAll c ctx.names M u) = .ok ())
    (htyp : OkOr (fun ty => OkOr (fun _ => True) (ops.ensureSort env
        (ctx.hiAt ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp).length) ty))
      (ops.inferType env
        (ctx.hiAt ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp).length) crest))
    (hside : ∀ f err st ks nds cur st',
      nestFields (nestPos ops env ctx f) (nestSyn ops env ctx f)
        ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp)
        (ctx.hiAt ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp).length) err nF 0 crest st
        = .ok (ks, nds, cur, st') →
      ((List.range nF).any fun i => ks.getD i .ordinary != .ordinary &&
        structUsedLater (closeTelescope nds
          (ctx.hiAt ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp).length) cur) 0 i)
        = false ∧
      (nestResHead cur && (cur.getAppArgs.drop ds.length).all (fun x => !x.nestOcc ctx.names
        ctx.nP (ctx.hiAt ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp).length)))
        = true) :
    CtorStep ops env ctx σ o ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp)
      (grpKeys us ds grp ++ act) us ds (grpSub us (ctx.hiAt wp.length) grp) cv nF := by
  obtain ⟨hsig, hna, self, fuelO, nb, hchk⟩ := hoff
  -- official's raw auxiliary constructor is the walk's constructor read back
  have hrb := rbE_instPisWith (ctx := ctx)
    (prog := (grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp) ds _ crest hcr
  rw [rbE_replaceConsts_grp _ hcl, hu] at hrb
  simp only [Option.some.injEq] at hrb
  subst hrb
  refine ⟨hnd, crest, sigmaAll c ctx.names M (rbE ctx _ crest), self, fuelO, nb, hcr,
    srel_rb hlv hso hclv hcps hcont hframe hsoff hind hfind hws hsc hsig hfr,
    sigmaAll_sigNF hσ hae hMaux hfind _ hsig hna, hpi, hchk, htyp, hside⟩

end Frame

end ConLeche
