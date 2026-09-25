module

public import ConLeche.Verify.Inductives.PosCompleteFrame
import ConLeche.Verify.Inductives.PosCompleteUnif
public import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Shift
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Verify.InferLemmas

public section

/-!
# The frames' obligations assembled (lane COMPLETE-4, (A))

`run_nr` (lane COMPLETE-3) proves (A) at the run under `Steps`: at every
fresh instantiation the walk meets, the frame's obligations.  This module
discharges `Steps` for the σ-world read off official's FINAL auxiliary map
`M` (`sigmaOfMap`: a frame's and a fresh key's auxiliary type is `M` at
the key's read-back), from

* the stack invariant `StepInv` (`StackOk`, `StackOff`, `FrameArity`,
  `ProgScoped`), preserved under every new frame (`stepInv_frame`);
* official's facts about `M`'s keys (`OffMap`: the elimination's
  whole-block copies, their heads, index counts and replaced constructors
  accepted by official's positivity loop — the ELIMINATION LINK's
  consumable form);
* the environment's facts (`EnvFacts`);
* the checks that are not positivity and the relational premises of the
  frame-constructor relation, per frame constructor (`FrameObl`):
  uniformity (`WShape`), freshness (`FreshOccs`), typing, U4, the
  formers' checks.

The result `steps_of`; `nestedBlockPositivity_of_map` composes it with
`nestedBlockPositivity_of_official`.
-/

namespace ConLeche

open Expr

section Steps

variable {ctx : NestCtx}

/-! ## Read-back agreement below a stack -/

/-- The hole constants agree below the older frames' holes. -/
theorem nestHoleConst_append {L wp : List NestHole} {i : Nat} (hi : i < ctx.hiAt wp.length) :
    nestHoleConst ctx (L ++ wp) i = nestHoleConst ctx wp i := by
  have hA : ∀ n, ctx.hiAt n = ctx.hiAt 0 + n := fun n => by simp [NestCtx.hiAt]
  have hwl : ctx.hiAt wp.length ≤ ctx.hiAt (L ++ wp).length := by
    rw [hA, hA (L ++ wp).length]; simp
  unfold nestHoleConst
  by_cases h1 : ctx.nP ≤ i ∧ i < ctx.hiAt 0
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : ctx.hiAt 0 ≤ i
    · have hlt : i - ctx.hiAt 0 < wp.length := by rw [hA] at hi; omega
      rw [if_pos ⟨h2, by omega⟩, if_pos ⟨h2, hi⟩]
      rw [List.reverse_append, List.getElem?_append_left (by simpa using hlt)]
    · rw [if_neg (by omega), if_neg (by omega)]

theorem replaceFVars_congr_wscoped {f g : Nat → Option Expr} {d : Nat}
    (hfg : ∀ i, i < d → f i = g i) : ∀ (x : Expr), Expr.WScoped d x →
      x.replaceFVars f = x.replaceFVars g := by
  intro x
  induction x with
  | fvar i ty _ =>
    intro h
    simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, hfg i h.1]
  | app f' a ihf iha =>
    intro h; simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, ihf h.1, iha h.2]
  | lam t b m iht ihb =>
    intro h; simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, iht h.1, ihb h.2]
  | forallE t b m iht ihb =>
    intro h; simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, iht h.1, ihb h.2]
  | letE t v b iht ihv ihb =>
    intro h; simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, iht h.1, ihv h.2.1, ihb h.2.2]
  | proj s i x ih =>
    intro h; simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, ih h]
  | bvar _ => intro _; rfl
  | sort _ => intro _; rfl
  | const _ _ => intro _; rfl
  | lit _ => intro _; rfl

/-- **A term scoped below the older frames reads back the same under a
longer stack.** -/
theorem rbE_append {L wp : List NestHole} {x : Expr}
    (hx : Expr.WScoped (ctx.hiAt wp.length) x) : rbE ctx (L ++ wp) x = rbE ctx wp x :=
  replaceFVars_congr_wscoped (fun _ hi => nestHoleConst_append hi) x hx

theorem rbKey_append {L wp : List NestHole} {K : NestKey}
    (hK : ∀ x ∈ K.ds, Expr.WScoped (ctx.hiAt wp.length) x) :
    rbKey ctx (L ++ wp) K = rbKey ctx wp K := by
  unfold rbKey
  congr 1
  exact List.map_congr_left fun x hx => rbE_append (hK x hx)

theorem wscoped_of_hasFvar_false {d : Nat} : ∀ {x : Expr}, x.hasFvar = false → Expr.WScoped d x := by
  intro x
  induction x with
  | fvar i ty _ => intro h; simp [Expr.hasFvar] at h
  | app f a ihf iha =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.WScoped]; exact ⟨ihf h.1, iha h.2⟩
  | lam t b m iht ihb =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.WScoped]; exact ⟨iht h.1, ihb h.2⟩
  | forallE t b m iht ihb =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.WScoped]; exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.WScoped]; exact ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | proj s i x ih =>
    intro h; simp only [Expr.hasFvar] at h
    simp only [Expr.WScoped]; exact ih h
  | bvar _ => intro _; simp [Expr.WScoped]
  | sort _ => intro _; simp [Expr.WScoped]
  | const _ _ => intro _; simp [Expr.WScoped]
  | lit _ => intro _; simp [Expr.WScoped]

/-- The frame stack an instantiation is walked under is a suffix of the
stack it was met under, and its parameters are scoped below it. -/
theorem nestWalkStack_facts {prog : List NestHole} {ds : List Expr}
    (hds : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x) :
    (∃ L, prog = L ++ nestWalkStack ctx prog ds) ∧
    ∀ x ∈ ds, Expr.WScoped (ctx.hiAt (nestWalkStack ctx prog ds).length) x := by
  unfold nestWalkStack
  split
  · rename_i hall
    refine ⟨⟨prog, by simp⟩, fun x hx => ?_⟩
    have hb : x.fvarB ≤ ctx.hiAt 0 := by
      have := List.all_eq_true.mp hall x hx
      simpa using this
    simpa using WScoped.of_fvarsBelow (hds x hx) (fvarB_le hb)
  · exact ⟨⟨[], by simp⟩, hds⟩

/-! ## The σ-world of official's final auxiliary map -/

/-- **The σ-world read off official's final auxiliary map `M`**: a frame's
hole and a fresh key stand for `M` at the key's read-back. -/
@[expose] def sigmaOfMap (ctx : NestCtx) (c : Official.ElimCtx) (isAux : Name → Bool)
    (M : List (Expr × Name)) : SigmaCtx where
  lvls := c.lvls
  ps := c.ps
  isAux := isAux
  frameAux prog h := M.lookup (rbKey ctx prog h.key)
  contAux prog K := M.lookup (rbKey ctx prog K)

/-- **The stack invariant**: the frames' keys read back to official's keys
(`StackOk`), their containers are stored inductives at their parameter
count (`StackOff`), their holes have official's arity (`FrameArity`),
and their parameters are scoped below the frames' holes (`ProgScoped`). -/
@[expose] def StepInv (ctx : NestCtx) (σ : SigmaCtx) (c : Official.ElimCtx)
    (o : Official.PosOracle) (prog : List NestHole) : Prop :=
  StackOk ctx σ prog ∧ StackOff c prog ∧ FrameArity ctx σ o prog ∧ ProgScoped ctx prog

theorem stepInv_nil {σ : SigmaCtx} {c : Official.ElimCtx} {o : Official.PosOracle} :
    StepInv ctx σ c o [] :=
  ⟨fun i h hk => by simp at hk, fun i h hk => by simp at hk, fun i h a hk => by simp at hk,
    fun i h hk => by simp at hk⟩

/-- **Official's facts about its final auxiliary map** — the consumable
form of the elimination link: every key is closed and mentions a member;
the head of every key is a stored inductive (not a member, not an
auxiliary type, not `Quot`) at its parameter count, with official's
arity; every key's whole container block is copied at the same
parameters; and every copied constructor, instantiated at the key's
parameters, is replaced against `M` (`SigOk`), free of auxiliary names,
and accepted by official's positivity loop at every fresh-local base
(official's verdict does not depend on the choice of fresh names). -/
structure OffMap (ctx : NestCtx) (c : Official.ElimCtx) (o : Official.PosOracle)
    (isAux : Name → Bool) (M : List (Expr × Name)) : Prop where
  keyOk : ∀ k a, M.lookup k = some a →
    k.looseBVarsBounded 0 = true ∧ k.nestOcc ctx.names 0 0 = true ∧ isAux a = true
  head : ∀ J us Ds a, M.lookup (Expr.mkAppN (.const J us) Ds) = some a →
    J ≠ quotName ∧ ctx.names.contains J = false ∧ isAux J = false ∧
    (∃ cv caps, c.find? J = some (.indInfo cv caps) ∧ caps.nparams = Ds.length) ∧
    nestArity ctx J = Ds.length + o.nIdx a
  block : ∀ C us Ds a, M.lookup (Expr.mkAppN (.const C us) Ds) = some a →
    ∀ J ∈ C :: nestFrameMates ctx C, ∃ aJ, M.lookup (Expr.mkAppN (.const J us) Ds) = some aJ
  ctors : ∀ J us Ds a, M.lookup (Expr.mkAppN (.const J us) Ds) = some a →
    ∀ cv nF, (cv, nF) ∈ c.ctorsOf J → ∃ u,
      instPisWith Ds (cv.type.instantiateLevelParams cv.levelParams us) = some u ∧
      SigOk c ctx.names M u ∧ NoAux isAux u ∧
      ∀ base, ctx.hiAt 0 ≤ base → ∃ self fuelO nb, o.names.contains self = true ∧
        Official.checkCtorPos o self fuelO nb base (sigmaAll c ctx.names M u) = .ok ()

/-- **Official's typing of its final auxiliary map** (from
`OfficialTypesAt`): every copied constructor, instantiated at its key
and replaced against `M`, typed by official at every fresh-local base;
every key typed in the final environment. -/
structure OffTyped (ctx : NestCtx) (c : Official.ElimCtx) (T : Official.TypingOracle)
    (M : List (Expr × Name)) : Prop where
  ctors : ∀ J us Ds a, M.lookup (Expr.mkAppN (.const J us) Ds) = some a →
    ∀ cv nF, (cv, nF) ∈ c.ctorsOf J → ∀ u,
      instPisWith Ds (cv.type.instantiateLevelParams cv.levelParams us) = some u →
      ∀ base, ctx.hiAt 0 ≤ base → T.ctorOk base (sigmaAll c ctx.names M u)
  nested : ∀ k a, M.lookup k = some a → T.nestedOk k

/-- **The environment's facts** the assembly reads: official's lookups
agree with the walk's off the members; official's constructor lists are
the walk's; a stored inductive's constructors carry its recorded
parameter count and bind their fields; the context's constants are
closed; constructor level parameters are distinct. -/
structure EnvFacts (ctx : NestCtx) (c : Official.ElimCtx) (isAux : Name → Bool) : Prop where
  ind : ∀ I cv caps, c.find? I = some (.indInfo cv caps) → ctx.names.contains I = false
  find : ∀ n, ctx.names.contains n = false → c.find? n = ctx.find? n
  ctorsOf : ∀ J, c.ctorsOf J = ((nestContainer ctx J).map (·.2)).getD []
  nparams : ∀ J cv caps, ctx.find? J = some (.indInfo cv caps) →
    ∃ L, nestContainer ctx J = some (caps.nparams, L)
  ctorArity : ∀ J n L, nestContainer ctx J = some (n, L) → ∀ x ∈ L, n + x.2 ≤ x.1.type.piArity
  closed : NestCtxOk ctx
  nodup : ∀ J n L, nestContainer ctx J = some (n, L) → ∀ x ∈ L, Name.nodup x.1.levelParams = true
  /-- every stored inductive passed official's `check_uniform_ind_occs` when
  official added it -/
  uniform : ∀ J cv caps, ctx.find? J = some (.indInfo cv caps) → ∀ L,
    nestContainer ctx J = some (caps.nparams, L) → ∀ x ∈ L,
      Official.uniformOcc caps.all (x.1.levelParams.map .param) caps.nparams 0 x.1.type = true
  /-- a container's frame group lies in each member's recorded block -/
  blockClosed : ∀ C J, J ∈ C :: nestFrameMates ctx C → ∀ n ∈ C :: nestFrameMates ctx C,
    (nestBlockOf ctx J).contains n = true
  /-- a stored constructor type mentions no member of the block being
  checked (declared later) and no auxiliary name (fresh) -/
  fresh : ∀ J n L, nestContainer ctx J = some (n, L) → ∀ x ∈ L,
    x.1.type.deepOcc (fun n => ctx.names.contains n || isAux n) = false
  /-- a stored constructor's type concludes, past its parameters and
  fields, in its own inductive at the constructor's level parameters, as
  many as the inductive's (the install's `checkSumCtor_shape`; official's
  `is_valid_ind_app`) -/
  ctorConcl : ∀ J cv caps, ctx.find? J = some (.indInfo cv caps) → ∀ n L,
    nestContainer ctx J = some (n, L) → ∀ x ∈ L,
      x.1.levelParams.length = cv.levelParams.length ∧ ∃ bs r,
        x.1.type.stripPis (n + x.2) = some (bs, r) ∧
        r.getAppFn = .const J (x.1.levelParams.map .param)

/-! ## The stack invariant under a new frame -/

/-- An entry of a stack grown by a frame: an older frame (same index) or
one of the frame's new entries. -/
theorem getElem?_frame {wp : List NestHole} {us : List Level} {ds : List Expr} {hi : Nat}
    {grp : List (Name × Expr)} {i : Nat} {h : NestHole}
    (hk : ((grpNews us ds hi grp).reverse ++ wp).reverse[i]? = some h) :
    wp.reverse[i]? = some h ∨ ∃ p ∈ grp, h = { key := ⟨p.1, us, ds⟩, base := hi } := by
  rw [List.reverse_append, List.reverse_reverse] at hk
  rcases Nat.lt_or_ge i wp.reverse.length with hi' | hi'
  · rw [List.getElem?_append_left hi'] at hk
    exact .inl hk
  · rw [List.getElem?_append_right hi'] at hk
    have := List.mem_of_getElem? hk
    simp only [grpNews, List.mem_map] at this
    obtain ⟨p, hp, rfl⟩ := this
    exact .inr ⟨p, hp, rfl⟩

/-- The walk stack of a key inherits the invariant. -/
theorem stepInv_walkStack {σ : SigmaCtx} {c : Official.ElimCtx} {o : Official.PosOracle}
    {prog : List NestHole} {ds : List Expr} (hI : StepInv ctx σ c o prog) :
    StepInv ctx σ c o (nestWalkStack ctx prog ds) := by
  unfold nestWalkStack
  split
  · exact stepInv_nil
  · exact hI

variable {c : Official.ElimCtx} {o : Official.PosOracle} {isAux : Name → Bool}
  {M : List (Expr × Name)}

/-- **The stack invariant under a new frame.**  At a fresh instantiation
`C.{us} ds` met under `prog` whose read-back is a key of `M`, the frame's
group (the container's whole block) pushed on the walk stack keeps the
invariant: the new entries read back to `M`'s whole-block copies at the
same parameters. -/
theorem stepInv_frame (hoff : OffMap ctx c o isAux M) {prog : List NestHole} {act : List NestKey}
    {C : Name} {us : List Level} {ds : List Expr} {a : Name} {grp : List (Name × Expr)}
    (hI : StepInv ctx (sigmaOfMap ctx c isAux M) c o prog)
    (ha : (sigmaOfMap ctx c isAux M).contAux prog ⟨C, us, ds⟩ = some a)
    (hk : ContKeyOk ctx isAux prog act C us ds) (hgrp : grp.map (·.1) = C :: nestFrameMates ctx C) :
    StepInv ctx (sigmaOfMap ctx c isAux M) c o
      ((grpNews us ds (ctx.hiAt (nestWalkStack ctx prog ds).length) grp).reverse ++
        nestWalkStack ctx prog ds) := by
  obtain ⟨-, -, hbv, hsc, -, -, -⟩ := hk
  obtain ⟨⟨L, hL⟩, hds⟩ := nestWalkStack_facts (ctx := ctx) hsc
  generalize hwp : nestWalkStack ctx prog ds = wp at hL hds ⊢
  have hIw : StepInv ctx (sigmaOfMap ctx c isAux M) c o wp := hwp ▸ stepInv_walkStack hI
  obtain ⟨hso, hsoff, har, hps⟩ := hIw
  generalize hN : grpNews us ds (ctx.hiAt wp.length) grp = N
  -- the key's read-back is a key of `M`, at the walk stack
  have hrbC : rbKey ctx prog ⟨C, us, ds⟩ = rbKey ctx wp ⟨C, us, ds⟩ := by
    rw [hL]; exact rbKey_append hds
  have hM : M.lookup (Expr.mkAppN (.const C us) (ds.map (rbE ctx wp))) = some a := by
    have : M.lookup (rbKey ctx prog ⟨C, us, ds⟩) = some a := ha
    rw [hrbC] at this; exact this
  -- every group entry reads back to a whole-block copy
  have hnew : ∀ p ∈ grp, ∃ aJ,
      rbKey ctx (N.reverse ++ wp) ⟨p.1, us, ds⟩ = Expr.mkAppN (.const p.1 us) (ds.map (rbE ctx wp)) ∧
      M.lookup (Expr.mkAppN (.const p.1 us) (ds.map (rbE ctx wp))) = some aJ := by
    intro p hp
    have hJ : p.1 ∈ C :: nestFrameMates ctx C := by
      rw [← hgrp]; exact List.mem_map_of_mem hp
    obtain ⟨aJ, hJM⟩ := hoff.block C us _ a hM p.1 hJ
    exact ⟨aJ, rbKey_append hds, hJM⟩
  -- an older frame's key reads back the same
  have hold : ∀ (i : Nat) (h : NestHole), wp.reverse[i]? = some h → rbKey ctx (N.reverse ++ wp) h.key = rbKey ctx wp h.key :=
    fun i h hh => rbKey_append (hps i h hh)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- StackOk
    intro i h hh
    rcases getElem?_frame (hN ▸ hh) with hh' | ⟨p, hp, rfl⟩
    · rw [hold i h hh']; exact hso i h hh'
    · obtain ⟨aJ, hrb, hJM⟩ := hnew p hp
      obtain ⟨hcl, hocc, -⟩ := hoff.keyOk _ _ hJM
      obtain ⟨-, hnm, hna, -⟩ := hoff.head _ _ _ _ hJM
      refine ⟨fun x hx => lbb_of_bvarB_zero (hbv x hx).1, ?_, ?_, hnm, hna⟩
      · rw [hrb]; exact hcl
      · rw [hrb]; exact hocc
  · -- StackOff
    intro i h hh
    rcases getElem?_frame (hN ▸ hh) with hh' | ⟨p, hp, rfl⟩
    · exact hsoff i h hh'
    · obtain ⟨aJ, -, hJM⟩ := hnew p hp
      obtain ⟨hq, -, -, ⟨cv, caps, hf, hnp⟩, -⟩ := hoff.head _ _ _ _ hJM
      exact ⟨hq, cv, caps, hf, by simpa using hnp⟩
  · -- FrameArity
    intro i h a' hh hfa
    have hfa' : M.lookup (rbKey ctx (N.reverse ++ wp) h.key) = some a' := hfa
    rcases getElem?_frame (hN ▸ hh) with hh' | ⟨p, hp, rfl⟩
    · rw [hold i h hh'] at hfa'
      exact har i h a' hh' hfa'
    · obtain ⟨aJ, hrb, -⟩ := hnew p hp
      rw [hrb] at hfa'
      obtain ⟨-, -, -, -, har'⟩ := hoff.head _ _ _ _ hfa'
      simpa using har'
  · -- ProgScoped
    rw [← hN]; exact ProgScoped.push hps hds grp

/-! ## Telescopes -/

theorem piArity_le_instantiate1 {v : Expr} : ∀ (e : Expr) (k : Nat),
    e.piArity ≤ (e.instantiate1 v k).piArity
  | .forallE t b m, k => by
    simp only [Expr.instantiate1, Expr.piArity]
    have := piArity_le_instantiate1 (v := v) b (k + 1)
    omega
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .app _ _, _ | .lam _ _ _, _
  | .letE _ _ _, _ | .lit _, _ | .proj _ _ _, _ => by simp [Expr.piArity]

theorem piArity_le_replaceConsts {f : Name → List Level → Option Expr} : ∀ (e : Expr),
    e.piArity ≤ (e.replaceConsts f).piArity
  | .forallE t b m => by
    simp only [Expr.replaceConsts, Expr.piArity]
    have := piArity_le_replaceConsts (f := f) b
    omega
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _
  | .letE _ _ _ | .lit _ | .proj _ _ _ => by simp [Expr.piArity]

theorem piArity_instantiateLevelParams {ks : List Name} {us : List Level} : ∀ (e : Expr),
    (e.instantiateLevelParams ks us).piArity = e.piArity
  | .forallE t b m => by
    simp only [Expr.instantiateLevelParams, Expr.piArity]
    rw [piArity_instantiateLevelParams b]
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _
  | .letE _ _ _ | .lit _ | .proj _ _ _ => by simp [Expr.instantiateLevelParams, Expr.piArity]

/-- A telescope instantiation succeeds on a term with enough syntactic
`Π`s, and leaves at least the rest. -/
theorem instPisWith_of_le_piArity : ∀ (ds : List Expr) (t : Expr), ds.length ≤ t.piArity →
    ∃ r, instPisWith ds t = some r ∧ t.piArity - ds.length ≤ r.piArity
  | [], t, _ => ⟨t, rfl, by simp⟩
  | d :: ds, .forallE a b m, h => by
    simp only [Expr.piArity, List.length_cons] at h
    have hle := piArity_le_instantiate1 (v := d) b 0
    obtain ⟨r, hr, hpr⟩ := instPisWith_of_le_piArity ds (b.instantiate1 d) (by omega)
    exact ⟨r, hr, by simp only [Expr.piArity, List.length_cons]; omega⟩
  | _ :: _, .bvar _, h | _ :: _, .fvar _ _, h | _ :: _, .sort _, h | _ :: _, .const _ _, h
  | _ :: _, .app _ _, h | _ :: _, .lam _ _ _, h | _ :: _, .letE _ _ _, h | _ :: _, .lit _, h
  | _ :: _, .proj _ _ _, h => by simp [Expr.piArity] at h

/-- The constructors of a group whose every container is stored at one
parameter count. -/
theorem groupCtors_of {n : Nat} : ∀ (names : List Name),
    (∀ J ∈ names, ∃ L, nestContainer ctx J = some (n, L)) →
    ∃ ctors, groupCtors ctx n names = some ctors ∧
      ∀ x ∈ ctors, ∃ J ∈ names, ∃ L, nestContainer ctx J = some (n, L) ∧ x ∈ L
  | [], _ => ⟨[], rfl, by simp⟩
  | J :: Js, h => by
    obtain ⟨L, hL⟩ := h J List.mem_cons_self
    obtain ⟨rest, hrest, hmem⟩ := groupCtors_of Js (fun J' hJ' => h J' (List.mem_cons_of_mem _ hJ'))
    refine ⟨L ++ rest, ?_, ?_⟩
    · simp [groupCtors, hL, hrest]
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ⟨J, List.mem_cons_self, L, hL, hx⟩
      · obtain ⟨J', hJ', L', hL', hx'⟩ := hmem x hx
        exact ⟨J', List.mem_cons_of_mem _ hJ', L', hL', hx'⟩

/-- The level parameters, instantiated at a list of their own length, are
that list. -/
theorem map_param_subst_nodup : ∀ {ks : List Name} {us : List Level}, Name.nodup ks = true →
    ks.length = us.length → (ks.map Level.param).map (Level.subst ks us) = us
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | k :: ks, v :: vs, hnd, hlen => by
    simp only [Name.nodup, Bool.and_eq_true, Bool.not_eq_true'] at hnd
    have hk : k ∉ ks := by simpa using hnd.1
    have hrest := map_param_subst_nodup (ks := ks) (us := vs) hnd.2 (by simpa using hlen)
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨by simp [Level.subst, Level.subst.go], ?_⟩
    have hcongr : (ks.map Level.param).map (Level.subst (k :: ks) (v :: vs))
        = (ks.map Level.param).map (Level.subst ks vs) := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro n hn
      have hne : k ≠ n := fun h => hk (h ▸ hn)
      simp [Level.subst, Level.subst.go, hne]
    rw [hcongr, hrest]

/-- The frame's substitution abstracts every member of its group at the
key's levels. -/
theorem grpSub_isSome {us : List Level} {hi : Nat} {grp : List (Name × Expr)} {c : Name}
    (hc : c ∈ grp.map (·.1)) : ∃ r, grpSub us hi grp c us = some r := by
  have hex : ∀ (L : List (Name × Expr)) (q : Name × Expr), q ∈ L → ∃ r, L.lookup q.1 = some r := by
    intro L
    induction L with
    | nil => intro q h; exact nomatch h
    | cons x xs ih =>
      intro q hq
      simp only [List.lookup]
      split
      · exact ⟨_, rfl⟩
      · rename_i hne
        rcases List.mem_cons.mp hq with rfl | hq
        · simp at hne
        · exact ih q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hp
  unfold grpSub
  rw [if_pos (by simp)]
  exact hex _ (grp[i].1, Expr.fvar (hi + i) grp[i].2) (List.mem_mapIdx.mpr ⟨i, hi', by simp⟩)

/-! ## The frames' obligations -/

/-- The per-frame obligations past the instantiation's own former check
(`FrameObl`'s rest): the group's formers' checks, and per frame
constructor the freshness of its syntactic occurrences. -/
@[expose] def FrameRest (ctx : NestCtx) (prog : List NestHole)
    (act : List NestKey) (C : Name) (us : List Level) (ds : List Expr) : Prop :=
  (∀ m ∈ C :: nestFrameMates ctx C, OkOr (fun _ => True)
    (nestInstType (m := CheckM) ctx (ctx.hiAt (nestWalkStack ctx prog ds).length) ⟨m, us, ds⟩)) ∧
  ∀ grp : List (Name × Expr), grp.map (·.1) = C :: nestFrameMates ctx C →
    (∀ p ∈ grp, ∃ nI, nestInstType (m := CheckM) ctx
      (ctx.hiAt (nestWalkStack ctx prog ds).length) ⟨p.1, us, ds⟩ = .ok (nI, p.2)) →
    ∀ J ∈ C :: nestFrameMates ctx C, ∀ L, nestContainer ctx J = some (ds.length, L) →
    ∀ cv nF, (cv, nF) ∈ L → ∀ crest,
      instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
        (grpSub us (ctx.hiAt (nestWalkStack ctx prog ds).length) grp)) = some crest →
      let prog' := (grpNews us ds (ctx.hiAt (nestWalkStack ctx prog ds).length) grp).reverse ++
        nestWalkStack ctx prog ds
      FreshOccs ctx prog' (grpKeys us ds grp ++ act) crest

/-- **The per-frame obligations the assembly does not discharge**: at a
fresh instantiation `C.{us} ds` met under `prog` (the stack invariant
holding, the read-back a key of `M`), the formers' checks (N2/N3, the
index count official's), the instantiation's typing (K.52), and at every
constructor of the frame's group — instantiated at the key, the group
abstracted — the frame-constructor relation's premises that are not
bookkeeping: FRESHNESS of its syntactic occurrences, its typing, and the
telescope's U4 check.  (The walk's shape — uniformity — is
derived from official's `check_uniform_ind_occs`, `EnvFacts.uniform`.) -/
@[expose] def FrameObl (ctx : NestCtx) (c : Official.ElimCtx)
    (o : Official.PosOracle) (isAux : Name → Bool) (M : List (Expr × Name)) : Prop :=
  ∀ prog act C us ds a, StepInv ctx (sigmaOfMap ctx c isAux M) c o prog →
    (sigmaOfMap ctx c isAux M).contAux prog ⟨C, us, ds⟩ = some a → ContKeyOk ctx isAux prog act C us ds →
    OkOr (fun r => r.1 = o.nIdx a)
      (nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨C, us, ds⟩) ∧
    FrameRest ctx prog act C us ds

/-- **`Steps` ASSEMBLED.**  For the σ-world of official's final auxiliary
map, the frames' obligations hold under the stack invariant, from
official's facts about the map (`OffMap`), the environment's
(`EnvFacts`) and the per-frame obligations (`FrameObl`). -/
theorem steps_of {ops : CheckerOps CheckM} {env : Env}
    (hσ : SigmaOk ctx (sigmaOfMap ctx c isAux M) o) (hae : AuxEnvOk ctx (sigmaOfMap ctx c isAux M))
    (hlv : c.lvls = ctx.lps.map .param) (hoff : OffMap ctx c o isAux M) (henv : EnvFacts ctx c isAux)
    (hobl : FrameObl ctx c o isAux M) {T : Official.TypingOracle}
    (hinf : InferSim ops env ctx (sigmaOfMap ctx c isAux M) T)
    (hu4 : U4Typed ops env ctx (sigmaOfMap ctx c isAux M) T) (hoT : OffTyped ctx c T M) :
    Steps ops env ctx (sigmaOfMap ctx c isAux M) o
      (fun prog _ => StepInv ctx (sigmaOfMap ctx c isAux M) c o prog) := by
  refine ⟨fun prog act hI => hI.2.2.1, ?_⟩
  intro prog act C us ds a hI ha hk
  have hk' := hk
  obtain ⟨hCn, -, hbv, hsc, -, -, -⟩ := hk'
  obtain ⟨⟨L0, hL0⟩, hds⟩ := nestWalkStack_facts (ctx := ctx) hsc
  obtain ⟨hinst, hmates, hgrpObl⟩ := hobl prog act C us ds a hI ha hk
  -- the key's read-back at the walk stack
  have hMC : M.lookup (Expr.mkAppN (.const C us) (ds.map (rbE ctx (nestWalkStack ctx prog ds))))
      = some a := by
    have h1 : M.lookup (rbKey ctx prog ⟨C, us, ds⟩) = some a := ha
    have h2 : rbKey ctx prog ⟨C, us, ds⟩ = rbKey ctx (nestWalkStack ctx prog ds) ⟨C, us, ds⟩ := by
      conv => lhs; rw [hL0]
      exact rbKey_append hds
    rw [h2] at h1; exact h1
  -- every group member is a stored container at the key's parameter count
  have hcont : ∀ J ∈ C :: nestFrameMates ctx C, ∃ aJ L,
      M.lookup (Expr.mkAppN (.const J us) (ds.map (rbE ctx (nestWalkStack ctx prog ds)))) = some aJ ∧
      nestContainer ctx J = some (ds.length, L) ∧ ∃ cv caps,
        ctx.find? J = some (.indInfo cv caps) ∧ caps.nparams = ds.length := by
    intro J hJ
    obtain ⟨aJ, hJM⟩ := hoff.block C us _ a hMC J hJ
    obtain ⟨-, hnm, -, ⟨cv, caps, hf, hnp⟩, -⟩ := hoff.head _ _ _ _ hJM
    rw [henv.find J hnm] at hf
    obtain ⟨L, hL⟩ := henv.nparams J cv caps hf
    exact ⟨aJ, L, hJM, by simpa [hnp] using hL, cv, caps, hf, by simpa using hnp⟩
  refine ⟨?_, hinst, hmates, ?_⟩
  · obtain ⟨-, L, -, hL, -⟩ := hcont C List.mem_cons_self
    exact ⟨L, hL⟩
  intro grp _ _ hmap hgi
  have hctor := hgrpObl grp hmap hgi
  have htyK := hinf.2 (nestWalkStack ctx prog ds) C us ds (hoT.nested _ a hMC)
  have hI' := stepInv_frame hoff hI ha hk hmap
  refine ⟨htyK, hI', ?_⟩
  obtain ⟨ctors, hgc, hmem⟩ := groupCtors_of (ctx := ctx) (n := ds.length) (C :: nestFrameMates ctx C)
    (fun J hJ => by obtain ⟨-, L, -, hL, -⟩ := hcont J hJ; exact ⟨L, hL⟩)
  refine ⟨ctors, by rw [hmap]; exact hgc, ?_⟩
  intro x hx
  obtain ⟨cv, nF⟩ := x
  obtain ⟨J, hJ, L, hL, hxL⟩ := hmem _ hx
  obtain ⟨aJ, -, hJM, -, cvJ, capsJ, hfJ, hnpJ⟩ := hcont J hJ
  have hwsds := hk.2.2.2.2.2.2.2
  generalize hwp : nestWalkStack ctx prog ds = wp at hds hMC hJM hI' hctor hgi hL0
  have hlen : ctx.hiAt wp.length ≤
      ctx.hiAt ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp).length := by
    simp [NestCtx.hiAt]
  -- the constructor's facts from the environment
  obtain ⟨nPc, hci⟩ := nestContainer_mem hL _ hxL
  have hcl0 : cv.type.hasFvar = false := henv.closed.1 _ hci
  have hcl : (cv.type.instantiateLevelParams cv.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hcl0
  have har := henv.ctorArity J _ L hL (cv, nF) hxL
  -- the walk's instantiated constructor
  obtain ⟨crest, hcr, hpr⟩ := instPisWith_of_le_piArity ds
    ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
      (grpSub us (ctx.hiAt wp.length) grp)) (by
        have := piArity_le_replaceConsts (f := grpSub us (ctx.hiAt wp.length) grp)
          (cv.type.instantiateLevelParams cv.levelParams us)
        rw [piArity_instantiateLevelParams] at this
        simp only at har; omega)
  have hpi : nF ≤ crest.piArity := by
    have := piArity_le_replaceConsts (f := grpSub us (ctx.hiAt wp.length) grp)
      (cv.type.instantiateLevelParams cv.levelParams us)
    rw [piArity_instantiateLevelParams] at this
    simp only at har; omega
  -- official's auxiliary constructor
  have hcv : (cv, nF) ∈ c.ctorsOf J := by rw [henv.ctorsOf J, hL]; simpa using hxL
  obtain ⟨u, hu, hsig, hna, hchk⟩ := hoff.ctors J us _ aJ hJM cv nF hcv
  have hds' : ds.map (rbE ctx ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp)) =
      ds.map (rbE ctx wp) := List.map_congr_left fun x hx => rbE_append (hds x hx)
  obtain ⟨self, fuelO, nb, hchk'⟩ :=
    hchk (ctx.hiAt ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp).length)
      (by simp [NestCtx.hiAt])
  have hfr := hctor J hJ L hL cv nF hxL crest hcr
  have hty := hoT.ctors J us _ aJ hJM cv nF hcv u hu
    (ctx.hiAt ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp).length) (by simp [NestCtx.hiAt])
  -- UNIFORMITY: the frame constructor has the walk's shape
  have hws : WShape ctx isAux ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp) crest := by
    have hLJ : nestContainer ctx J = some (capsJ.nparams, L) := by rw [hnpJ]; exact hL
    have hu := henv.uniform J cvJ capsJ hfJ L hLJ (cv, nF) hxL
    rw [hnpJ] at hu
    refine wshape_frameCtor (names := capsJ.all) (lvls := cv.levelParams.map .param)
      (fun n hn => ?_) (fun x hx => ⟨?_, lbb_of_bvarB_zero (hbv x hx).1⟩)
      (Nat.le_trans (Nat.le_add_right _ nF) har)
      hu hcl0 (henv.fresh J _ L hL (cv, nF) hxL) hcr
    · rw [hmap] at hn
      have := henv.blockClosed C J hJ n hn
      simpa [nestBlockOf, hfJ] using this
    · refine WShape.restack (Q := wp) (fun i hi => ?_) (fun i hi => ?_) (hwsds x hx) (hds x hx)
      · rw [hL0, List.reverse_append, List.getElem?_append_left (by simpa using hi)]
      · rw [List.reverse_append, List.reverse_reverse,
          List.getElem?_append_left (by simpa using hi)]
  -- the scoping of the instantiated constructor
  have hsc' : Expr.WScoped
      (ctx.hiAt ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp).length) crest := by
    refine wscoped_instPisWith (fun x hx => WScoped.mono hlen (hds x hx)) ?_ hcr
    refine WScoped.replaceConsts_closed ?_ _ hcl
    intro n us' e he
    simp only [grpSub] at he
    split at he
    · obtain ⟨i, hi, h1, h2⟩ := lookup_mem_name he
      simp only [List.length_mapIdx] at hi
      simp only [List.getElem_mapIdx] at h2
      subst h2
      simp only [Expr.WScoped]
      refine ⟨by simp [NestCtx.hiAt, grpNews]; omega, ?_⟩
      obtain ⟨nI, hnI⟩ := hgi grp[i] (List.getElem_mem hi)
      exact wscoped_of_hasFvar_false (nestInstType_closed henv.closed hnI)
    · exact nomatch he
  -- the frame constructor's conclusion: the hole of its own inductive
  have hhead : ∃ bs r k ty, crest.stripPis nF = some (bs, r) ∧ r.getAppFn = .fvar k ty ∧
      ctx.hiAt wp.length ≤ k := by
    obtain ⟨hlvJ, bs, r, hs, hr⟩ := henv.ctorConcl J cvJ capsJ hfJ _ L hL (cv, nF) hxL
    simp only at hlvJ hs hr
    have hJg : J ∈ grp.map (·.1) := by rw [hmap]; exact hJ
    obtain ⟨p, hp, hpJ⟩ := List.mem_map.mp hJg
    obtain ⟨nI, hnI⟩ := hgi p hp
    obtain ⟨cvP, capsP, hfP, hlvP⟩ := nestInstType_lvls hnI
    have hlvP' : us.length = cvP.levelParams.length := hlvP
    have hfP' : ctx.find? J = some (.indInfo cvP capsP) := by rw [← hpJ]; exact hfP
    rw [hfJ] at hfP'
    cases hfP'
    obtain ⟨bs₁, hs₁⟩ := stripPis_instLP (ks := cv.levelParams) (us := us) _ _ hs
    have hr₁ : (r.instantiateLevelParams cv.levelParams us).getAppFn = .const J us := by
      rw [getAppFn_instantiateLevelParams, hr]
      simp only [Expr.instantiateLevelParams]
      have hnd : Name.nodup cv.levelParams = true := henv.nodup J _ L hL (cv, nF) hxL
      rw [map_param_subst_nodup hnd (by omega)]
    obtain ⟨hole, hhole⟩ := grpSub_isSome (us := us) (hi := ctx.hiAt wp.length) hJg
    obtain ⟨i, hi, rfl⟩ := grpSub_hole hhole
    obtain ⟨bs₂, hs₂⟩ := stripPis_replaceConsts (f := grpSub us (ctx.hiAt wp.length) grp) _ _ hs₁
    have hr₂ : ((r.instantiateLevelParams cv.levelParams us).replaceConsts
        (grpSub us (ctx.hiAt wp.length) grp)).getAppFn = .fvar (ctx.hiAt wp.length + i) grp[i].2 := by
      rw [← Expr.mkAppN_getApp (r.instantiateLevelParams cv.levelParams us), hr₁,
        replaceConsts_mkAppN, Expr.getAppFn_mkAppN]
      simp [Expr.replaceConsts, hhole, Expr.getAppFn]
    obtain ⟨bs₃, r₃, hs₃, hr₃⟩ := fvHead_instPisWith ds _ nF hs₂ hr₂ hcr
    exact ⟨bs₃, r₃, _, _, hs₃, hr₃, Nat.le_add_right _ _⟩
  subst hwp
  exact ctorStep_of hσ hae hlv (M := M) (hI'.1) hI'.2.1 rfl rfl (fun _ => rfl) (fun _ _ _ => rfl)
    henv.ind henv.find (fun k x hx => (hoff.keyOk k x hx).2.2)
    (henv.nodup J _ L hL (cv, nF) hxL) hcl hcr (by rw [hds']; exact hu) hws hsc' hfr hpi
    ⟨hsig, hna, self, fuelO, nb, hchk'⟩ hinf hu4 hty hhead

/-- **(A) FOR A NESTED BLOCK, FROM OFFICIAL'S FINAL AUXILIARY MAP.**  With
the σ-world read off official's final map `M` (`sigmaOfMap`), official's
facts about `M` (`OffMap`), the environment's (`EnvFacts`), the per-frame
obligations (`FrameObl`: uniformity, freshness, typing, U4, the
formers' checks) and `WhnfSim`: if official's positivity loop accepts
every member constructor's replacement, the walk's
`nestedBlockPositivity` succeeds or declines — it never rejects. -/
theorem nestedBlockPositivity_of_map {ops : CheckerOps CheckM} {env : Env}
    (hσ : SigmaOk ctx (sigmaOfMap ctx c isAux M) o) (hae : AuxEnvOk ctx (sigmaOfMap ctx c isAux M))
    (hsim : WhnfSim ops env ctx (sigmaOfMap ctx c isAux M) o.whnf)
    (hlv : c.lvls = ctx.lps.map .param) (hoff : OffMap ctx c o isAux M) (henv : EnvFacts ctx c isAux)
    (hobl : FrameObl ctx c o isAux M) {T : Official.TypingOracle}
    (hinf : InferSim ops env ctx (sigmaOfMap ctx c isAux M) T)
    (hu4 : U4Typed ops env ctx (sigmaOfMap ctx c isAux M) T) (hoT : OffTyped ctx c T M)
    {holes : List Expr}
    (hholes : nestHoles ctx = some holes) (hh : HolesOk ctx holes) (hps : ParamsOk ctx isAux)
    {ctorss : List (List (ConstantVal × Nat))}
    (hall : ∀ cs ∈ ctorss, ∀ cc ∈ cs, ∃ u,
      cc.1.type.hasFvar = false ∧ Good ctx isAux cc.1.type ∧
      instPisWith ctx.params cc.1.type = some u ∧ SigOk c ctx.names M u ∧
      (∃ self fuelO nb, ctx.names.contains self = true ∧
        Official.checkCtorPos o self fuelO nb (ctx.hiAt 0) (sigmaAll c ctx.names M u) = .ok ()) ∧
      T.ctorOk (ctx.hiAt 0) (sigmaAll c ctx.names M u) ∧
      (∀ crest, instPisWith ctx.params (nestAbstract ctx holes cc.1.type) = some crest →
        crest.piArity = cc.2 ∧ MemberSide ops env ctx cc.2 crest) ∧
      (nestAbstract ctx holes cc.1.type).nestOcc ctx.names 0 0 = false) :
    OkOr (fun _ => True) (nestedBlockPositivity ops env ctx ctorss) :=
  nestedBlockPositivity_of_official hσ hae hsim hu4 (steps_of hσ hae hlv hoff henv hobl hinf hu4 hoT)
    stepInv_nil
    hholes hh hlv hps rfl rfl (fun _ => rfl) henv.ind henv.find
    (fun k x hx => (hoff.keyOk k x hx).2.2) hall

end Steps

end ConLeche
