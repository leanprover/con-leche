module

public import ConLeche.Verify.Inductives.PosDerivComplete
import ConLeche.Verify.Inductives.PosDerivInv
public import ConLeche.Verify.Inductives.OfficialNested
import ConLeche.Verify.Subst
import ConLeche.Verify.Shift
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Cached.Erase

public section

/-!
# Official's positivity ⇒ the run-complete derivation, one frame level (lane COMPLETE-2, half (A))

The walk (`nestPos`) and official's `check_positivity` (`OfficialNested.lean`)
read two different worlds:

* the WALK's: the members are the hole variables `nP + t`; an
  instantiation in progress is its frame's hole applied to its key's
  parameters (`h ds`); an instantiation met is a container application
  `C Ds` (a constant);
* OFFICIAL's (σ): the members are constants `T`; every nested occurrence
  it replaced syntactically is an auxiliary constant applied to the
  parameters, `auxI ps` — whether our side walks it as a frame's hole or
  meets it as a container application.

`SRel` relates the two: congruence, plus three base cases (a member hole ↔
its constant; a frame hole at its key ↔ its auxiliary type; a FRESH
container application `C Ds` ↔ its auxiliary type).  Every σ-occurrence
of a declared type comes from a base case, and conversely
(`SRel.occ_of`, `SRel.of_occ`).

**The named hypothesis** (the maintainer's "whnf does not observe
replacing a container application by an opaque constant"):
`WhnfSim ops env ctx σ whnfσ` — whnf in the σ-world (the members and the
auxiliary types opaque) succeeding on a σ-term implies our whnf succeeds on
every `SRel`-related walk term, with `SRel`-related results.  It is the
exact form the simulation consumes; "some occurrences replaced" is built
into `SRel` (a container application may stay a constant on both sides:
congruence), so a δ-step that EXPOSES a container on both sides is
admitted, and official then rejects it (a non-valid occurrence).

**What is proved here** (`posA_field`): at ONE frame level — a field
under the frame stack `prog` with in-progress list `act` — official's
`check_positivity` accepting the σ-term gives a `PosDR` derivation of
the walk term, given (i) `WhnfSim`, (ii) `ContProv`: every fresh
container instantiation the σ-side reads as an auxiliary type has its
frame derived (the recursion into frames: the remaining obligation),
and (iii) the frame holes' arity agreeing with official's index count.
`posA_tele`/`memberCtorDR_of_official` lift it to a member constructor
(given the syntactic pass's derivations, `SynProv`, and the
non-positivity checks U4, M3/M2′, result), and `nestMemberCtor_of_official`
composes with (B): the run succeeds.
-/

namespace ConLeche

open Expr

/-- The σ-world's data the relation reads: official's levels and
parameters, which names are auxiliary types, and which auxiliary type
each frame and each fresh container instantiation stands for. -/
structure SigmaCtx where
  lvls : List Level
  ps : List Expr
  isAux : Name → Bool
  /-- the auxiliary type a frame's hole stands for, under the frames `prog`
  (a hole's key reads back through the frames below it, so the map
  depends on the stack) -/
  frameAux : List NestHole → NestHole → Option Name
  /-- the auxiliary type a container instantiation stands for, under the
  frames `prog` -/
  contAux : List NestHole → NestKey → Option Name

/-- Does a constant satisfying `p` occur in `e`, fvar annotations
included? -/
@[expose] def Expr.deepOcc (p : Name → Bool) : Expr → Bool
  | .bvar _ | .sort _ | .lit _ => false
  | .fvar _ ty => deepOcc p ty
  | .const n _ => p n
  | .app f a => deepOcc p f || deepOcc p a
  | .lam t b _ | .forallE t b _ => deepOcc p t || deepOcc p b
  | .letE t v b => deepOcc p t || deepOcc p v || deepOcc p b
  | .proj _ _ x => deepOcc p x

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

/-- **A container instantiation met as a constant, as the walk's `cont`
rule needs it**: not a member, not `Quot`, parameters closed and scoped
below the frames' holes, mentioning a hole or member, and FRESH (in no
frame of `prog`, not in progress). -/
@[expose] def ContKeyOk (ctx : NestCtx) (isAux : Name → Bool) (prog : List NestHole)
    (act : List NestKey) (C : Name) (us : List Level) (ds : List Expr) : Prop :=
  ctx.names.contains C = false ∧ C ≠ quotName ∧
  (∀ x ∈ ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length) ∧
  (∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x) ∧
  (∃ x ∈ ds, x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true) ∧
  (∀ h ∈ prog, h.key ≠ ⟨C, us, ds⟩) ∧ (⟨C, us, ds⟩ : NestKey) ∉ act ∧
  (∀ x ∈ ds, WShape ctx isAux prog x)

/-- **A walk term read back** under the frames `prog`: every hole back to
its constant (`nestHoleConst`: a member hole to its member, a frame's
hole to its group member at the frame's levels). -/
@[expose] def rbE (ctx : NestCtx) (prog : List NestHole) (x : Expr) : Expr :=
  x.replaceFVars (nestHoleConst ctx prog)

/-- **A key read back** under the frames `prog`: official's key `J Ds`. -/
@[expose] def rbKey (ctx : NestCtx) (prog : List NestHole) (K : NestKey) : Expr :=
  Expr.mkAppN (.const K.cname K.lvls) (K.ds.map (rbE ctx prog))

/-- **The σ-relation**: the walk term (left) and official's term (right)
under the frames `prog` and the in-progress list `act` (see the module
doc). -/
inductive SRel (ctx : NestCtx) (σ : SigmaCtx) (prog : List NestHole) (act : List NestKey) :
    Expr → Expr → Prop where
  /-- a member hole is its member constant -/
  | mem {t : Nat} {ty : Expr} (ht : t < ctx.names.length) :
      SRel ctx σ prog act (.fvar (ctx.nP + t) ty) (.const (ctx.names.getD t .anonymous) σ.lvls)
  /-- a frame's hole at its key is its auxiliary type at the parameters -/
  | frm {i : Nat} {ty : Expr} {h : NestHole} {a : Name} (hk : prog.reverse[i]? = some h)
      (ha : σ.frameAux prog h = some a) (hcl : ∀ x ∈ h.key.ds, x.looseBVarsBounded 0 = true) :
      SRel ctx σ prog act (Expr.mkAppN (.fvar (ctx.hiAt 0 + i) ty) h.key.ds)
        (Expr.mkAppN (.const a σ.lvls) σ.ps)
  /-- a frame's hole at its key, UNREPLACED on the σ-side (a position
  official's replacement does not traverse — an auxiliary type's raw
  indices): its read-back `J Ds` -/
  | raw {i : Nat} {ty : Expr} {h : NestHole} (hk : prog.reverse[i]? = some h)
      (hcl : ∀ x ∈ h.key.ds, x.looseBVarsBounded 0 = true)
      (hrcl : (rbKey ctx prog h.key).looseBVarsBounded 0 = true)
      (hocc : (rbKey ctx prog h.key).nestOcc ctx.names 0 0 = true)
      (hnm : ctx.names.contains h.key.cname = false) (hna : σ.isAux h.key.cname = false) :
      SRel ctx σ prog act (Expr.mkAppN (.fvar (ctx.hiAt 0 + i) ty) h.key.ds) (rbKey ctx prog h.key)
  /-- a fresh container instantiation is its auxiliary type at the parameters -/
  | cnt {C : Name} {us : List Level} {ds : List Expr} {a : Name}
      (ha : σ.contAux prog ⟨C, us, ds⟩ = some a) (hk : ContKeyOk ctx σ.isAux prog act C us ds) :
      SRel ctx σ prog act (Expr.mkAppN (.const C us) ds) (Expr.mkAppN (.const a σ.lvls) σ.ps)
  | bvar (i : Nat) : SRel ctx σ prog act (.bvar i) (.bvar i)
  | sort (u : Level) : SRel ctx σ prog act (.sort u) (.sort u)
  | lit (l : Literal) : SRel ctx σ prog act (.lit l) (.lit l)
  | const {n : Name} {us : List Level} (hn : ctx.names.contains n = false)
      (ha : σ.isAux n = false) : SRel ctx σ prog act (.const n us) (.const n us)
  | fvar {i : Nat} {ty ty' : Expr} (hi : i < ctx.nP ∨ ctx.hiAt prog.length ≤ i)
      (hty : SRel ctx σ prog act ty ty') : SRel ctx σ prog act (.fvar i ty) (.fvar i ty')
  | app {f a f' a' : Expr} : SRel ctx σ prog act f f' → SRel ctx σ prog act a a' →
      SRel ctx σ prog act (.app f a) (.app f' a')
  | lam {t b t' b' : Expr} {m : BinderMeta} : SRel ctx σ prog act t t' →
      SRel ctx σ prog act b b' → SRel ctx σ prog act (.lam t b m) (.lam t' b' m)
  | forallE {t b t' b' : Expr} {m : BinderMeta} : SRel ctx σ prog act t t' →
      SRel ctx σ prog act b b' → SRel ctx σ prog act (.forallE t b m) (.forallE t' b' m)
  | letE {t v b t' v' b' : Expr} : SRel ctx σ prog act t t' → SRel ctx σ prog act v v' →
      SRel ctx σ prog act b b' → SRel ctx σ prog act (.letE t v b) (.letE t' v' b')
  | proj {s : Name} {i : Nat} {x x' : Expr} : SRel ctx σ prog act x x' →
      SRel ctx σ prog act (.proj s i x) (.proj s i x')

/-- **THE NAMED HYPOTHESIS: whnf does not observe the σ-replacement.**
Whnf in the σ-world succeeding on official's term implies the walk's whnf
succeeds on every related walk term, with related results. -/
@[expose] def WhnfSim (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (σ : SigmaCtx)
    (whnfσ : Nat → Expr → Except CheckError Expr) : Prop :=
  ∀ (prog : List NestHole) (act : List NestKey) (dep : Nat) (e e' w' : Expr),
    ctx.hiAt prog.length ≤ dep → SRel ctx σ prog act e e' → whnfσ dep e' = .ok w' →
    ∃ w, ops.whnf env dep e = .ok w ∧ SRel ctx σ prog act w w'

/-- Two lists related pointwise. -/
inductive Rel2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Rel2 R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → Rel2 R as bs →
      Rel2 R (a :: as) (b :: bs)

theorem Rel2.append {α β : Type} {R : α → β → Prop} :
    ∀ {as bs : List α} {cs ds : List β}, Rel2 R as cs → Rel2 R bs ds → Rel2 R (as ++ bs) (cs ++ ds)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h₁ h₂, h => .cons h₁ (Rel2.append h₂ h)

theorem Rel2.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Rel2 R as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [h.length_eq]

theorem Rel2.take {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) {as : List α} {bs : List β}, Rel2 R as bs → Rel2 R (as.take n) (bs.take n)
  | 0, _, _, _ => by simpa using Rel2.nil
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons h₁ h₂ => .cons h₁ (Rel2.take n h₂)

theorem Rel2.drop {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) {as : List α} {bs : List β}, Rel2 R as bs → Rel2 R (as.drop n) (bs.drop n)
  | 0, _, _, h => by simpa using h
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons _ h₂ => by simpa using Rel2.drop n h₂

theorem Rel2.forall_left {α β : Type} {R : α → β → Prop} {P : α → Prop} {Q : β → Prop}
    (hPQ : ∀ a b, R a b → Q b → P a) :
    ∀ {as : List α} {bs : List β}, Rel2 R as bs → (∀ b ∈ bs, Q b) → ∀ a ∈ as, P a
  | _, _, .nil, _, _, ha => nomatch ha
  | _, _, .cons h₁ h₂, hq, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hPQ _ _ h₁ (hq _ List.mem_cons_self)
    · exact Rel2.forall_left hPQ h₂ (fun b hb => hq b (List.mem_cons_of_mem _ hb)) a ha

theorem Rel2.eq_of {α : Type} {R : α → α → Prop} (hR : ∀ a b, R a b → a = b) :
    ∀ {as bs : List α}, Rel2 R as bs → as = bs
  | _, _, .nil => rfl
  | _, _, .cons h₁ h₂ => by rw [hR _ _ h₁, Rel2.eq_of hR h₂]

/-- The σ-world is consistent with the walk's context: official's declared
names are the members and the auxiliary types (disjoint), its parameters
are the walk's (closed, and mentioning no declared type even in their
annotations — `ParamsFree`), each member's index count is official's, and
every frame's and fresh key's auxiliary type is an auxiliary name. -/
structure SigmaOk (ctx : NestCtx) (σ : SigmaCtx) (o : Official.PosOracle) : Prop where
  names : ∀ n, o.names.contains n = (ctx.names.contains n || σ.isAux n)
  disj : ∀ n, σ.isAux n = true → ctx.names.contains n = false
  lvls : o.lvls = σ.lvls
  ps : o.ps = σ.ps
  psEq : σ.ps = ctx.params
  psLen : ctx.params.length = ctx.nP
  psFvar : ∀ i (h : i < ctx.params.length), ∃ ty, ctx.params[i] = .fvar i ty ∧
    ty.deepOcc (o.names.contains ·) = false
  psClosed : ∀ p ∈ σ.ps, p.looseBVarsBounded 0 = true
  nIdx : ∀ t, t < ctx.names.length → o.nIdx (ctx.names.getD t .anonymous) = ctx.nIdxs.getD t 0
  frameAux : ∀ prog h a, σ.frameAux prog h = some a → σ.isAux a = true
  contAux : ∀ prog k a, σ.contAux prog k = some a → σ.isAux a = true

section Lemmas

variable {ctx : NestCtx} {σ : SigmaCtx} {prog : List NestHole} {act : List NestKey}

theorem nestOcc_mkAppN (names : List Name) (lo hi : Nat) :
    ∀ (args : List Expr) (f : Expr),
      (Expr.mkAppN f args).nestOcc names lo hi =
        (f.nestOcc names lo hi || args.any (·.nestOcc names lo hi))
  | [], f => by simp [Expr.mkAppN]
  | a :: as, f => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl, nestOcc_mkAppN _ _ _ as]
    simp [Expr.nestOcc, Bool.or_assoc]

theorem nestOcc_names_mono {names names' : List Name}
    (hmono : ∀ n, names.contains n = true → names'.contains n = true) :
    ∀ (e : Expr), e.nestOcc names 0 0 = true → e.nestOcc names' 0 0 = true := by
  intro e
  induction e with
  | const n us => simpa [Expr.nestOcc] using hmono n
  | app f a ihf iha =>
    simp only [Expr.nestOcc, Bool.or_eq_true]
    rintro (h | h)
    · exact .inl (ihf h)
    · exact .inr (iha h)
  | lam t b _ iht ihb | forallE t b _ iht ihb =>
    simp only [Expr.nestOcc, Bool.or_eq_true]
    rintro (h | h)
    · exact .inl (iht h)
    · exact .inr (ihb h)
  | letE t v b iht ihv ihb =>
    simp only [Expr.nestOcc, Bool.or_eq_true]
    rintro ((h | h) | h)
    · exact .inl (.inl (iht h))
    · exact .inl (.inr (ihv h))
    · exact .inr (ihb h)
  | proj _ _ x ih => simpa [Expr.nestOcc] using ih
  | _ => simp [Expr.nestOcc]

theorem deepOcc_of_nestOcc {names : List Name} {p : Name → Bool}
    (hp : ∀ n, names.contains n = true → p n = true) :
    ∀ (e : Expr), e.nestOcc names 0 0 = true → e.deepOcc p = true := by
  intro e
  induction e with
  | const n us => simpa [Expr.nestOcc, Expr.deepOcc] using hp n
  | app f a ihf iha =>
    simp only [Expr.nestOcc, Expr.deepOcc, Bool.or_eq_true]
    rintro (h | h)
    · exact .inl (ihf h)
    · exact .inr (iha h)
  | lam t b _ iht ihb | forallE t b _ iht ihb =>
    simp only [Expr.nestOcc, Expr.deepOcc, Bool.or_eq_true]
    rintro (h | h)
    · exact .inl (iht h)
    · exact .inr (ihb h)
  | letE t v b iht ihv ihb =>
    simp only [Expr.nestOcc, Expr.deepOcc, Bool.or_eq_true]
    rintro ((h | h) | h)
    · exact .inl (.inl (iht h))
    · exact .inl (.inr (ihv h))
    · exact .inr (ihb h)
  | proj _ _ x ih => simpa [Expr.nestOcc, Expr.deepOcc] using ih
  | _ => simp [Expr.nestOcc]

/-- A walk occurrence (a member, a hole) is a σ-occurrence. -/
theorem SRel.occ_of {o : Official.PosOracle} (hσ : SigmaOk ctx σ o) {x x' : Expr}
    (h : SRel ctx σ prog act x x') :
    x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true → o.occ x' = true := by
  induction h with
  | @mem t ty ht =>
    intro _
    simp only [Official.PosOracle.occ, Expr.nestOcc, hσ.names, Bool.or_eq_true]
    left
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
    simp [List.getElem_mem ht]
  | frm hk ha hcl =>
    intro _
    simp only [Official.PosOracle.occ, nestOcc_mkAppN, Expr.nestOcc, hσ.names, hσ.frameAux _ _ _ ha,
      Bool.or_true, Bool.true_or]
  | raw _ _ _ hocc _ _ =>
    intro _
    exact nestOcc_names_mono (fun n hn => by rw [hσ.names, hn, Bool.true_or]) _ hocc
  | cnt ha hk =>
    intro _
    simp only [Official.PosOracle.occ, nestOcc_mkAppN, Expr.nestOcc, hσ.names, hσ.contAux _ _ _ ha,
      Bool.or_true, Bool.true_or]
  | bvar i => simp [Expr.nestOcc]
  | sort u => simp [Expr.nestOcc]
  | lit l => simp [Expr.nestOcc]
  | const hn ha =>
    intro h
    simp only [Expr.nestOcc, hn] at h
    exact absurd h (by simp)
  | fvar hi hty _ =>
    intro h
    simp only [Expr.nestOcc, decide_eq_true_eq] at h
    simp only [NestCtx.hiAt] at hi h
    omega
  | app _ _ ihf iha =>
    simp only [Official.PosOracle.occ, Expr.nestOcc, Bool.or_eq_true] at ihf iha ⊢
    rintro (h | h)
    · exact Or.inl (ihf h)
    · exact Or.inr (iha h)
  | lam _ _ iht ihb | forallE _ _ iht ihb =>
    simp only [Official.PosOracle.occ, Expr.nestOcc, Bool.or_eq_true] at iht ihb ⊢
    rintro (h | h)
    · exact Or.inl (iht h)
    · exact Or.inr (ihb h)
  | letE _ _ _ iht ihv ihb =>
    simp only [Official.PosOracle.occ, Expr.nestOcc, Bool.or_eq_true] at iht ihv ihb ⊢
    rintro ((h | h) | h)
    · exact Or.inl (Or.inl (iht h))
    · exact Or.inl (Or.inr (ihv h))
    · exact Or.inr (ihb h)
  | proj _ ih =>
    simp only [Official.PosOracle.occ, Expr.nestOcc] at ih ⊢
    exact ih

/-- A σ-occurrence is a walk occurrence. -/
theorem SRel.of_occ {o : Official.PosOracle} (hσ : SigmaOk ctx σ o) {x x' : Expr}
    (h : SRel ctx σ prog act x x') :
    o.occ x' = true → x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true := by
  induction h with
  | @mem t ty ht =>
    intro _
    simp only [Expr.nestOcc, NestCtx.hiAt]
    exact decide_eq_true ⟨by omega, by omega⟩
  | @frm i ty h a hk ha hcl =>
    intro _
    have hi : i < prog.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      simpa using this
    simp only [nestOcc_mkAppN, Expr.nestOcc, NestCtx.hiAt, Bool.or_eq_true, decide_eq_true_eq]
    left; omega
  | @raw i ty h hk _ _ _ _ _ =>
    intro _
    have hi : i < prog.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      simpa using this
    simp only [nestOcc_mkAppN, Expr.nestOcc, NestCtx.hiAt, Bool.or_eq_true, decide_eq_true_eq]
    left; omega
  | cnt ha hk =>
    intro _
    obtain ⟨x, hx, hxo⟩ := hk.2.2.2.2.1
    simp only [nestOcc_mkAppN, Bool.or_eq_true, List.any_eq_true]
    exact Or.inr ⟨x, hx, hxo⟩
  | bvar i => simp [Official.PosOracle.occ, Expr.nestOcc]
  | sort u => simp [Official.PosOracle.occ, Expr.nestOcc]
  | lit l => simp [Official.PosOracle.occ, Expr.nestOcc]
  | const hn ha =>
    intro h
    simp only [Official.PosOracle.occ, Expr.nestOcc, hσ.names, hn, ha] at h
    exact absurd h (by simp)
  | fvar hi hty _ => simp [Official.PosOracle.occ, Expr.nestOcc]
  | app _ _ ihf iha =>
    simp only [Official.PosOracle.occ, Expr.nestOcc, Bool.or_eq_true] at ihf iha ⊢
    rintro (h | h)
    · exact Or.inl (ihf h)
    · exact Or.inr (iha h)
  | lam _ _ iht ihb | forallE _ _ iht ihb =>
    simp only [Official.PosOracle.occ, Expr.nestOcc, Bool.or_eq_true] at iht ihb ⊢
    rintro (h | h)
    · exact Or.inl (iht h)
    · exact Or.inr (ihb h)
  | letE _ _ _ iht ihv ihb =>
    simp only [Official.PosOracle.occ, Expr.nestOcc, Bool.or_eq_true] at iht ihv ihb ⊢
    rintro ((h | h) | h)
    · exact Or.inl (Or.inl (iht h))
    · exact Or.inl (Or.inr (ihv h))
    · exact Or.inr (ihb h)
  | proj _ ih =>
    simp only [Official.PosOracle.occ, Expr.nestOcc] at ih ⊢
    exact ih

theorem deepOcc_mkAppN (p : Name → Bool) :
    ∀ (args : List Expr) (f : Expr),
      (Expr.mkAppN f args).deepOcc p = (f.deepOcc p || args.any (·.deepOcc p))
  | [], f => by simp [Expr.mkAppN]
  | a :: as, f => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl, deepOcc_mkAppN _ as]
    simp [Expr.deepOcc, Bool.or_assoc]

/-- **The spine inversion**: a σ-term headed by a declared type's
constant comes from a base case — a member's from the member's hole, an
auxiliary type's from a frame's hole at its key or a fresh container
application — with the remaining arguments related. -/
theorem SRel.spine {o : Official.PosOracle} (hσ : SigmaOk ctx σ o) {x x' : Expr}
    (h : SRel ctx σ prog act x x') :
    ∀ {n : Name} {us' : List Level}, x'.getAppFn = .const n us' →
    (ctx.names.contains n = true → ∃ t ty, t < ctx.names.length ∧
      x.getAppFn = .fvar (ctx.nP + t) ty ∧ ctx.names.getD t .anonymous = n ∧ us' = σ.lvls ∧
      Rel2 (SRel ctx σ prog act) x.getAppArgs x'.getAppArgs) ∧
    (σ.isAux n = true → us' = σ.lvls ∧ ∃ is is', x'.getAppArgs = σ.ps ++ is' ∧
      Rel2 (SRel ctx σ prog act) is is' ∧
      ((∃ i ty hk, prog.reverse[i]? = some hk ∧ σ.frameAux prog hk = some n ∧
          (∀ y ∈ hk.key.ds, y.looseBVarsBounded 0 = true) ∧
          x = Expr.mkAppN (Expr.mkAppN (.fvar (ctx.hiAt 0 + i) ty) hk.key.ds) is) ∨
       (∃ C us ds, σ.contAux prog ⟨C, us, ds⟩ = some n ∧ ContKeyOk ctx σ.isAux prog act C us ds ∧
          x = Expr.mkAppN (Expr.mkAppN (.const C us) ds) is))) := by
  induction h with
  | @mem t ty ht =>
    intro n us' hfn
    simp only [Expr.getAppFn, Expr.const.injEq] at hfn
    obtain ⟨rfl, rfl⟩ := hfn
    refine ⟨fun _ => ⟨t, ty, ht, rfl, rfl, rfl, .nil⟩, fun haux => ?_⟩
    have hc := hσ.disj _ haux
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht] at hc
    simp [List.getElem_mem ht] at hc
  | @frm i ty hk a hk' ha hcl =>
    intro n us' hfn
    rw [Expr.getAppFn_mkAppN] at hfn
    simp only [Expr.getAppFn, Expr.const.injEq] at hfn
    obtain ⟨rfl, rfl⟩ := hfn
    refine ⟨fun hc => ?_, fun _ => ⟨rfl, [], [], ?_, .nil, Or.inl ⟨i, ty, hk, hk', ha, hcl, rfl⟩⟩⟩
    · rw [hσ.disj _ (hσ.frameAux _ _ _ ha)] at hc; exact nomatch hc
    · rw [Expr.getAppArgs_mkAppN]; simp [Expr.getAppArgs]
  | @raw i ty hk _ _ _ _ hnm hna =>
    intro n us' hfn
    simp only [rbKey] at hfn
    rw [Expr.getAppFn_mkAppN] at hfn
    simp only [Expr.getAppFn, Expr.const.injEq] at hfn
    obtain ⟨rfl, rfl⟩ := hfn
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [hnm] at hc; exact nomatch hc
    · rw [hna] at hc; exact nomatch hc
  | @cnt C us ds a ha hk =>
    intro n us' hfn
    rw [Expr.getAppFn_mkAppN] at hfn
    simp only [Expr.getAppFn, Expr.const.injEq] at hfn
    obtain ⟨rfl, rfl⟩ := hfn
    refine ⟨fun hc => ?_, fun _ => ⟨rfl, [], [], ?_, .nil, Or.inr ⟨C, us, ds, ha, hk, rfl⟩⟩⟩
    · rw [hσ.disj _ (hσ.contAux _ _ _ ha)] at hc; exact nomatch hc
    · rw [Expr.getAppArgs_mkAppN]; simp [Expr.getAppArgs]
  | bvar i => intro n us' hfn; simp [Expr.getAppFn] at hfn
  | sort u => intro n us' hfn; simp [Expr.getAppFn] at hfn
  | lit l => intro n us' hfn; simp [Expr.getAppFn] at hfn
  | const hn ha =>
    intro n us' hfn
    simp only [Expr.getAppFn, Expr.const.injEq] at hfn
    obtain ⟨rfl, rfl⟩ := hfn
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [hn] at hc; exact nomatch hc
    · rw [ha] at hc; exact nomatch hc
  | fvar _ _ _ => intro n us' hfn; simp [Expr.getAppFn] at hfn
  | lam _ _ _ _ => intro n us' hfn; simp [Expr.getAppFn] at hfn
  | forallE _ _ _ _ => intro n us' hfn; simp [Expr.getAppFn] at hfn
  | letE _ _ _ _ _ _ => intro n us' hfn; simp [Expr.getAppFn] at hfn
  | proj _ _ => intro n us' hfn; simp [Expr.getAppFn] at hfn
  | @app f a f' a' hf ha ihf iha =>
    intro n us' hfn
    simp only [Expr.getAppFn] at hfn
    obtain ⟨h1, h2⟩ := ihf hfn
    refine ⟨fun hc => ?_, fun haux => ?_⟩
    · obtain ⟨t, ty, ht, hfx, hn, hus, hargs⟩ := h1 hc
      refine ⟨t, ty, ht, by simpa [Expr.getAppFn] using hfx, hn, hus, ?_⟩
      simp only [Expr.getAppArgs]
      exact Rel2.append hargs (.cons ha .nil)
    · obtain ⟨hus, is, is', hargs, hrel, hcase⟩ := h2 haux
      refine ⟨hus, is ++ [a], is' ++ [a'], ?_, Rel2.append hrel (.cons ha .nil), ?_⟩
      · simp [Expr.getAppArgs, hargs]
      · rcases hcase with ⟨i, ty, hk, hk', hfa, hcl, rfl⟩ | ⟨C, us, ds, hca, hok, rfl⟩
        · exact Or.inl ⟨i, ty, hk, hk', hfa, hcl, by rw [Expr.mkAppN_append_one]⟩
        · exact Or.inr ⟨C, us, ds, hca, hok, by rw [Expr.mkAppN_append_one]⟩

/-- **The Π inversion**: a σ-term that is a `Π` is related from a `Π`. -/
theorem SRel.forallE_inv {x a' b' : Expr} {bm : BinderMeta}
    (h : SRel ctx σ prog act x (.forallE a' b' bm)) :
    ∃ a b, x = .forallE a b bm ∧ SRel ctx σ prog act a a' ∧ SRel ctx σ prog act b b' := by
  generalize hx : Expr.forallE a' b' bm = x' at h
  cases h with
  | forallE ht hb =>
    simp only [Expr.forallE.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨_, _, rfl, ht, hb⟩
  | frm _ _ _ =>
    have := congrArg Expr.getAppFn hx
    rw [Expr.getAppFn_mkAppN] at this
    simp [Expr.getAppFn] at this
  | raw _ _ _ _ _ _ =>
    have := congrArg Expr.getAppFn hx
    simp only [rbKey] at this
    rw [Expr.getAppFn_mkAppN] at this
    simp [Expr.getAppFn] at this
  | cnt _ _ =>
    have := congrArg Expr.getAppFn hx
    rw [Expr.getAppFn_mkAppN] at this
    simp [Expr.getAppFn] at this
  | _ => simp at hx

/-- A σ-term with no declared type anywhere (annotations included) is
related only from itself. -/
theorem SRel.eq_of_deepFree {o : Official.PosOracle} (hσ : SigmaOk ctx σ o) {x x' : Expr}
    (h : SRel ctx σ prog act x x') (hd : x'.deepOcc (o.names.contains ·) = false) : x = x' := by
  induction h with
  | @mem t ty ht =>
    simp only [Expr.deepOcc, hσ.names] at hd
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht] at hd
    simp [List.getElem_mem ht] at hd
  | frm _ ha _ =>
    simp only [deepOcc_mkAppN, Expr.deepOcc, hσ.names, hσ.frameAux _ _ _ ha] at hd
    simp at hd
  | raw _ _ _ hocc _ _ =>
    rw [deepOcc_of_nestOcc (fun n hn => by rw [hσ.names, hn, Bool.true_or]) _ hocc] at hd
    exact nomatch hd
  | cnt ha _ =>
    simp only [deepOcc_mkAppN, Expr.deepOcc, hσ.names, hσ.contAux _ _ _ ha] at hd
    simp at hd
  | bvar i => rfl
  | sort u => rfl
  | lit l => rfl
  | const _ _ => rfl
  | fvar _ _ ih =>
    simp only [Expr.deepOcc] at hd
    rw [ih hd]
  | app _ _ ihf iha =>
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hd
    rw [ihf hd.1, iha hd.2]
  | lam _ _ iht ihb | forallE _ _ iht ihb =>
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hd
    rw [iht hd.1, ihb hd.2]
  | letE _ _ _ iht ihv ihb =>
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hd
    rw [iht hd.1.1, ihv hd.1.2, ihb hd.2]
  | proj _ ih =>
    simp only [Expr.deepOcc] at hd
    rw [ih hd]

theorem map_instantiate1_closed {v : Expr} {k : Nat} :
    ∀ (ds : List Expr), (∀ x ∈ ds, x.looseBVarsBounded 0 = true) →
      ds.map (·.instantiate1 v k) = ds
  | [], _ => rfl
  | d :: ds, h => by
    simp only [List.map_cons]
    rw [Expr.instantiate1_eq_self (Expr.looseBVarsBounded_mono (Nat.zero_le k)
      (h d List.mem_cons_self)), map_instantiate1_closed ds (fun x hx => h x
      (List.mem_cons_of_mem _ hx))]

/-- **The relation is a congruence for instantiation** at related
values. -/
theorem SRel.instantiate1 {o : Official.PosOracle} (hσ : SigmaOk ctx σ o) {v v' : Expr}
    (hv : SRel ctx σ prog act v v') {x x' : Expr} (h : SRel ctx σ prog act x x') :
    ∀ k, SRel ctx σ prog act (x.instantiate1 v k) (x'.instantiate1 v' k) := by
  induction h with
  | mem ht => intro k; exact .mem ht
  | @frm i ty hk a hk' ha hcl =>
    intro k
    rw [Expr.mkAppN_instantiate1, Expr.mkAppN_instantiate1, map_instantiate1_closed _ hcl,
      map_instantiate1_closed _ hσ.psClosed]
    exact .frm hk' ha hcl
  | @raw i ty h hk hcl hrcl hocc hnm hna =>
    intro k
    rw [Expr.mkAppN_instantiate1, map_instantiate1_closed _ hcl,
      Expr.instantiate1_eq_self (Expr.looseBVarsBounded_mono (Nat.zero_le k) hrcl)]
    exact .raw hk hcl hrcl hocc hnm hna
  | @cnt C us ds a ha hk =>
    intro k
    rw [Expr.mkAppN_instantiate1, Expr.mkAppN_instantiate1,
      map_instantiate1_closed _ (fun x hx => Expr.bvarB_le (Nat.le_of_eq (hk.2.2.1 x hx).1)),
      map_instantiate1_closed _ hσ.psClosed]
    exact .cnt ha hk
  | bvar i =>
    intro k
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split
      · exact .bvar _
      · exact .bvar _
  | sort u => intro k; exact .sort u
  | lit l => intro k; exact .lit l
  | const hn ha => intro k; exact .const hn ha
  | fvar hi hty _ => intro k; exact .fvar hi hty
  | app _ _ ihf iha => intro k; exact .app (ihf k) (iha k)
  | lam _ _ iht ihb => intro k; exact .lam (iht k) (ihb (k + 1))
  | forallE _ _ iht ihb => intro k; exact .forallE (iht k) (ihb (k + 1))
  | letE _ _ _ iht ihv ihb => intro k; exact .letE (iht k) (ihv k) (ihb (k + 1))
  | proj _ ih => intro k; exact .proj (ih k)

theorem Rel2.eq_params {o : Official.PosOracle} (hσ : SigmaOk ctx σ o) :
    ∀ {as ps : List Expr}, Rel2 (SRel ctx σ prog act) as ps →
      (∀ p ∈ ps, p.deepOcc (o.names.contains ·) = false) → as = ps
  | _, _, .nil, _ => rfl
  | _, _, .cons h₁ h₂, hd => by
    rw [h₁.eq_of_deepFree hσ (hd _ List.mem_cons_self),
      Rel2.eq_params hσ h₂ (fun p hp => hd p (List.mem_cons_of_mem _ hp))]

end Lemmas

/-! ## The simulation at one frame level -/

/-- **The recursion into frames — the remaining obligation of (A).** Every
fresh container instantiation official reads as an auxiliary type has its
container's constructors (at the key's parameter count), its former
checked (N2/N3) with official's index count, and its frame derived at the
walk stack. -/
@[expose] def ContProv (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (σ : SigmaCtx)
    (o : Official.PosOracle) (prog : List NestHole) (act : List NestKey) : Prop :=
  ∀ C us ds a, σ.contAux prog ⟨C, us, ds⟩ = some a → ContKeyOk ctx σ.isAux prog act C us ds →
    ∃ m grp L nI cty, nestContainer ctx C = some (ds.length, L) ∧
      nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨C, us, ds⟩ = .ok (nI, cty) ∧
      nI = o.nIdx a ∧ (grp.headD default).1 = C ∧
      PosDR ops env ctx m (.frame act (nestWalkStack ctx prog ds) us ds grp)

/-- The frames' holes have official's arity: the container's parameters and
its auxiliary type's indices. -/
@[expose] def FrameArity (ctx : NestCtx) (σ : SigmaCtx) (o : Official.PosOracle)
    (prog : List NestHole) : Prop :=
  ∀ (i : Nat) (h : NestHole) (a : Name), prog.reverse[i]? = some h → σ.frameAux prog h = some a →
    nestArity ctx h.key.cname = h.key.ds.length + o.nIdx a

section Field

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {σ : SigmaCtx}
  {o : Official.PosOracle}

/-- **(A) AT ONE FRAME LEVEL.**  Under `WhnfSim`, official's
`check_positivity` accepting a σ-term makes the related walk term's field
judgment derivable (`PosDR`), given the frames of the fresh instantiations
it meets (`ContProv`) and the frame holes' arity (`FrameArity`). -/
theorem posA_field (hσ : SigmaOk ctx σ o) (hsim : WhnfSim ops env ctx σ o.whnf)
    {prog : List NestHole} {act : List NestKey} (hsc : ProgScoped ctx prog)
    (hprov : ContProv ops env ctx σ o prog act) (harity : FrameArity ctx σ o prog) :
    ∀ fuel dep kb e e', ctx.hiAt prog.length ≤ dep → SRel ctx σ prog act e e' →
      Official.checkPositivity o fuel dep e' = .ok () →
      ∃ n k nf, PosDR ops env ctx n (.field act prog dep kb e k nf) := by
  intro fuel
  induction fuel with
  | zero =>
    intro dep kb e e' _ _ hchk
    simp [Official.checkPositivity, throw, throwThe, MonadExceptOf.throw] at hchk
  | succ fuel ih =>
    intro dep kb e e' hdep hrel hchk
    simp only [Official.checkPositivity, bind, Except.bind] at hchk
    split at hchk
    · simp at hchk
    rename_i w' hw'
    obtain ⟨w, hw, hrw⟩ := hsim prog act dep e e' w' hdep hrel hw'
    by_cases hocc : o.occ w' = true
    · rw [if_neg (by simp [hocc])] at hchk
      have hwocc := hrw.of_occ hσ hocc
      split at hchk
      · -- a Π
        rename_i a' b' bm
        by_cases ha' : o.occ a' = true
        · rw [if_pos ha'] at hchk
          simp [throw, throwThe, MonadExceptOf.throw] at hchk
        rw [if_neg ha'] at hchk
        obtain ⟨a, b, rfl, hra, hrb⟩ := hrw.forallE_inv
        have ha : a.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false := by
          cases hc : a.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length)
          · rfl
          · exact absurd (hra.occ_of hσ hc) ha'
        have hrb' := SRel.instantiate1 hσ (.fvar (Or.inr hdep) hra) hrb 0
        obtain ⟨n, k, nf, hd⟩ := ih (dep + 1) (kb + 1) _ _ (by omega) hrb' hchk
        exact ⟨n + 1, k, _, .pi hw hwocc ha (Nat.lt_succ_self n) hd⟩
      · -- a valid application of a declared type
        rename_i hnpi
        by_cases hv : o.valid w' = true
        · clear hchk
          simp only [Official.PosOracle.valid, List.any_eq_true] at hv
          obtain ⟨n0, hn0, hva⟩ := hv
          simp only [Official.PosOracle.validAt, Bool.and_eq_true, beq_iff_eq] at hva
          obtain ⟨⟨⟨hfn', hlen'⟩, htake'⟩, hdrop'⟩ := hva
          have hn0' : (ctx.names.contains n0 || σ.isAux n0) = true := by
            rw [← hσ.names]; simpa using hn0
          have hdrop'' : ∀ x ∈ w'.getAppArgs.drop o.ps.length, o.occ x = false := by
            intro x hx
            have := List.all_eq_true.mp hdrop' x hx
            simpa using this
          have hfree_of : ∀ (xs xs' : List Expr), Rel2 (SRel ctx σ prog act) xs xs' →
              (∀ x ∈ xs', o.occ x = false) →
              ∀ x ∈ xs, x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false := by
            intro xs xs' hr hq
            refine Rel2.forall_left (fun a b hab hb => ?_) hr hq
            cases hc : a.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length)
            · rfl
            · rw [hab.occ_of hσ hc] at hb; exact nomatch hb
          obtain ⟨h1, h2⟩ := hrw.spine hσ hfn'
          rcases Bool.or_eq_true_iff.mp hn0' with hmem | haux
          · -- a member: the walk's `hole`
            obtain ⟨t, ty, ht, hfx, hnm, -, hargs⟩ := h1 hmem
            have hpsl : o.ps.length = ctx.nP := by rw [hσ.ps, hσ.psEq, hσ.psLen]
            have hlen : w.getAppArgs.length = ctx.nP + ctx.nIdxs.getD (ctx.nP + t - ctx.nP) 0 := by
              rw [hargs.length_eq, hlen', hpsl, ← hnm, hσ.nIdx t ht]
              simp
            have hpar : w.getAppArgs.take ctx.nP = ctx.params := by
              have h3 := Rel2.take o.ps.length hargs
              rw [htake', hpsl, hσ.ps, hσ.psEq] at h3
              refine Rel2.eq_params hσ h3 (fun p hp => ?_)
              obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
              obtain ⟨ty', hpi, hty'⟩ := hσ.psFvar i hi
              rw [hpi]
              simpa [Expr.deepOcc] using hty'
            have hfree : ∀ x ∈ w.getAppArgs,
                x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false := by
              intro x hx
              rw [← List.take_append_drop ctx.nP w.getAppArgs] at hx
              rcases List.mem_append.mp hx with hx | hx
              · rw [hpar] at hx
                obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
                obtain ⟨ty', hpi, -⟩ := hσ.psFvar i hi
                rw [hpi]
                have : i < ctx.nP := by rw [← hσ.psLen]; exact hi
                simp only [Expr.nestOcc, decide_eq_false_iff_not, not_and, Nat.not_lt]
                omega
              · have h3 := Rel2.drop ctx.nP hargs
                rw [← hpsl] at h3
                exact hfree_of _ _ h3 hdrop'' x (by rw [hpsl] at *; exact hx)
            exact ⟨0 + 1, _, _, .hole hw hwocc hfx (by omega) (by simp [NestCtx.hiAt]; omega)
              hlen hpar hfree⟩
          · -- an auxiliary type: a frame's hole, or a fresh container
            obtain ⟨-, is, is', hargs', hrel', hcase⟩ := h2 haux
            have hps' : o.ps = σ.ps := hσ.ps
            have hislen : is'.length = o.nIdx n0 := by
              rw [hargs', List.length_append, hps'] at hlen'; omega
            have hisq : ∀ x ∈ is', o.occ x = false := by
              intro x hx
              apply hdrop''
              rw [hargs', hps', List.drop_left]
              exact hx
            have hisfree := hfree_of _ _ hrel' hisq
            have hisl : is.length = is'.length := hrel'.length_eq
            rcases hcase with ⟨i, ty, hk, hk', hfa, hcl, rfl⟩ | ⟨C, us, ds, hca, hok, rfl⟩
            · have hi : i < prog.length := by
                have := (List.getElem?_eq_some_iff.mp hk').1
                simpa using this
              have hA : (Expr.mkAppN (Expr.mkAppN (.fvar (ctx.hiAt 0 + i) ty) hk.key.ds) is).getAppArgs
                  = hk.key.ds ++ is := by
                rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN]; simp [Expr.getAppArgs]
              refine ⟨0 + 1, _, _, .frameHole (i := ctx.hiAt 0 + i) (ty := ty) hw hwocc ?_
                (by omega) (by simp only [NestCtx.hiAt]; omega) (h := hk) ?_ ?_ ?_ ?_ ?_⟩
              · rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN]; rfl
              · simpa using hk'
              · rw [hA]; simp
              · rw [hA]; simp
              · rw [hA]; simpa using hisfree
              · rw [hA, List.length_append, harity i hk n0 hk' hfa, hisl, hislen]
            · obtain ⟨m, grp, L, nI, cty, hC, hnI, hnIe, hhead, hfr⟩ := hprov C us ds n0 hca hok
              have hA : (Expr.mkAppN (Expr.mkAppN (.const C us) ds) is).getAppArgs = ds ++ is := by
                rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN]; simp [Expr.getAppArgs]
              have htk : (Expr.mkAppN (Expr.mkAppN (.const C us) ds) is).getAppArgs.take ds.length
                  = ds := by rw [hA]; simp
              refine ⟨m + 1, _, _, PosDR.cont (c := C) (us := us) (nPc := ds.length) (nI := nI) (L := L) (cty := cty)
                (grp := grp) hw hwocc ?_ hok.1 hC ?_ hok.2.1 ?_ ?_ ?_ hsc ?_ ?_ ?_ hhead
                (Nat.lt_succ_self m) ?_⟩
              · rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN]; rfl
              · rw [hA, List.length_append, hisl, hislen, hnIe]
              · rw [hA]; simpa using hisfree
              · rw [htk]; exact hok.2.2.1
              · rw [htk]; exact hok.2.2.2.1
              · rw [htk]; exact hnI
              · rw [htk]; exact hok.2.2.2.2.2.1
              · rw [htk]; exact hok.2.2.2.2.2.2.1
              · rw [htk]; exact hfr
        · rw [if_neg hv] at hchk
          simp [throw, throwThe, MonadExceptOf.throw] at hchk
    · -- no declared type: the walk's `const`
      have hwn : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false := by
        cases hc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length)
        · rfl
        · exact absurd (hrw.occ_of hσ hc) hocc
      exact ⟨0 + 1, _, _, .const hw hwn⟩

end Field

/-! ## Lifting to a telescope and a member constructor -/

/-! The syntactic `Π` count of a term (`Expr.piArity`) is kept by
instantiation at a variable (`piArity_instantiate1`). -/

theorem piArity_instantiate1 {i : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), (e.instantiate1 (.fvar i ty) k).piArity = e.piArity
  | .forallE t b m, k => by
    simp only [Expr.instantiate1, Expr.piArity]
    rw [piArity_instantiate1 b (k + 1)]
  | .bvar j, k => by
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | .fvar _ _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .app _ _, _ => rfl
  | .lam _ _ _, _ => rfl
  | .letE _ _ _, _ => rfl
  | .lit _, _ => rfl
  | .proj _ _ _, _ => rfl

theorem SRel.forallE_inv_left {ctx : NestCtx} {σ : SigmaCtx} {prog : List NestHole}
    {act : List NestKey} {a b x' : Expr} {bm : BinderMeta}
    (h : SRel ctx σ prog act (.forallE a b bm) x') :
    ∃ a' b', x' = .forallE a' b' bm ∧ SRel ctx σ prog act a a' ∧ SRel ctx σ prog act b b' := by
  generalize hx : Expr.forallE a b bm = x at h
  cases h with
  | forallE ht hb =>
    simp only [Expr.forallE.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨_, _, rfl, ht, hb⟩
  | frm _ _ _ =>
    have := congrArg Expr.getAppFn hx
    rw [Expr.getAppFn_mkAppN] at this
    simp [Expr.getAppFn] at this
  | raw _ _ _ _ _ _ =>
    have := congrArg Expr.getAppFn hx
    rw [Expr.getAppFn_mkAppN] at this
    simp [Expr.getAppFn] at this
  | cnt _ _ =>
    have := congrArg Expr.getAppFn hx
    rw [Expr.getAppFn_mkAppN] at this
    simp [Expr.getAppFn] at this
  | _ => simp at hx

/-- **The syntactic pass's derivations — the second remaining obligation
of (A)**: every field domain official's `check_positivity` accepts (a
related σ-term) has its syntactic occurrences derived. -/
@[expose] def SynProv (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (σ : SigmaCtx)
    (o : Official.PosOracle) (prog : List NestHole) (act : List NestKey) : Prop :=
  ∀ fuel dep a a', ctx.hiAt prog.length ≤ dep → SRel ctx σ prog act a a' →
    Official.checkPositivity o fuel dep a' = .ok () →
    ∃ m, PosDR ops env ctx m (.synKeys act prog a (nestSynOccs ctx (ctx.hiAt prog.length) a))

theorem checkCtorPos_valid {o : Official.PosOracle} {self : Name} {fuel nb dep : Nat} {t : Expr}
    (h : Official.checkCtorPos o self fuel (nb + 1) dep t = .ok ())
    (hnpi : ∀ a b bm, t ≠ .forallE a b bm) : o.validAt self t = true := by
  cases t with
  | forallE a b bm => exact absurd rfl (hnpi a b bm)
  | _ =>
    simp only [Official.checkCtorPos] at h
    split at h
    · assumption
    · simp [throw, throwThe, MonadExceptOf.throw] at h

section Tele

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {σ : SigmaCtx}
  {o : Official.PosOracle}

/-- **(A) at a telescope**: official's field loop (`checkCtorPos`)
accepting a σ-constructor makes `nF` fields of the related walk
constructor derivable, the rest related and still accepted. -/
theorem posA_tele (hσ : SigmaOk ctx σ o) (hsim : WhnfSim ops env ctx σ o.whnf)
    {prog : List NestHole} {act : List NestKey} (hsc : ProgScoped ctx prog)
    (hprov : ContProv ops env ctx σ o prog act) (harity : FrameArity ctx σ o prog)
    (hsyn : SynProv ops env ctx σ o prog act) {self : Name} {fuel base : Nat}
    (hbase : ctx.hiAt prog.length ≤ base) :
    ∀ (nF j : Nat) (cur ct' : Expr) (nb : Nat), SRel ctx σ prog act cur ct' → nF ≤ cur.piArity →
      Official.checkCtorPos o self fuel nb (base + j) ct' = .ok () →
      ∃ n ks nds res res' nb', PosDR ops env ctx n (.tele act prog base nF j cur ks nds res) ∧
        SRel ctx σ prog act res res' ∧ res.piArity = cur.piArity - nF ∧
        Official.checkCtorPos o self fuel nb' (base + j + nF) res' = .ok () := by
  intro nF
  induction nF with
  | zero =>
    intro j cur ct' nb hrel _ hchk
    exact ⟨0, [], [], cur, ct', nb, .teleNil, hrel, by simp, hchk⟩
  | succ nF ih =>
    intro j cur ct' nb hrel hpi hchk
    cases cur with
    | forallE a b bm =>
      obtain ⟨a', b', rfl, hra, hrb⟩ := hrel.forallE_inv_left
      cases nb with
      | zero => simp [Official.checkCtorPos, throw, throwThe, MonadExceptOf.throw] at hchk
      | succ nb =>
        simp only [Official.checkCtorPos, bind, Except.bind] at hchk
        split at hchk
        · simp at hchk
        rename_i u hpos
        obtain ⟨n₁, k, nd, hd₁⟩ := posA_field hσ hsim hsc hprov harity fuel (base + j) 0 a a'
          (by omega) hra hpos
        obtain ⟨m₂, hd₂⟩ := hsyn fuel (base + j) a a' (by omega) hra hpos
        have hrb' := SRel.instantiate1 hσ (.fvar (i := base + j) (Or.inr (by omega)) hra) hrb 0
        have hpi' : nF ≤ (b.instantiate1 (.fvar (base + j) a)).piArity := by
          rw [piArity_instantiate1]; simp only [Expr.piArity] at hpi; omega
        obtain ⟨n₃, ks, nds, res, res', nb', hd₃, hrr, hpar, hchk'⟩ :=
          ih (j + 1) _ _ nb hrb' hpi' (by rw [show base + (j + 1) = base + j + 1 by omega]; exact hchk)
        refine ⟨n₁ + m₂ + n₃ + 1, k :: ks, (nd, bm) :: nds, res, res', nb',
          .teleCons (by omega) hd₁ (by omega) hd₂ (by omega) hd₃, hrr, ?_, ?_⟩
        · rw [hpar, piArity_instantiate1]; simp [Expr.piArity]
        · rw [show base + j + (nF + 1) = base + (j + 1) + nF by omega]; exact hchk'
    | _ => simp [Expr.piArity] at hpi

/-- **(A) at a member constructor**: official accepting the σ-constructor
(`checkCtorPos` at the member) makes the walk constructor's telescope
derivable at no frame, with a result headed by the member's hole and
hole-free indices — every part of `MemberCtorDR` except U4 and M3/M2′,
which are not positivity. -/
theorem posA_member (hσ : SigmaOk ctx σ o) (hsim : WhnfSim ops env ctx σ o.whnf)
    (hprov : ContProv ops env ctx σ o [] []) (hsyn : SynProv ops env ctx σ o [] [])
    {self : Name} (hself : ctx.names.contains self = true) {fuel nb nF : Nat} {crest ct' : Expr}
    (hrel : SRel ctx σ [] [] crest ct') (hpi : crest.piArity = nF)
    (hchk : Official.checkCtorPos o self fuel nb (ctx.hiAt 0) ct' = .ok ()) :
    ∃ n ks nds cur, PosDR ops env ctx n (.tele [] [] (ctx.hiAt 0) nF 0 crest ks nds cur) ∧
      nestResHead cur = true ∧
      (cur.getAppArgs.drop ctx.nP).all (fun a => !a.nestOcc ctx.names ctx.nP (ctx.hiAt 0)) = true := by
  have harity : FrameArity ctx σ o [] := fun i h a hk => by simp at hk
  obtain ⟨n, ks, nds, res, res', nb', hd, hrr, hpar, hchk'⟩ :=
    posA_tele hσ hsim ProgScoped.nil hprov harity hsyn (base := ctx.hiAt 0) (Nat.le_refl _) nF 0
      crest ct' nb hrel (by omega) (by simpa using hchk)
  refine ⟨n, ks, nds, res, hd, ?_⟩
  -- the result is not a Π: official checks it is valid at the member
  have hres0 : res.piArity = 0 := by omega
  cases nb' with
  | zero => simp [Official.checkCtorPos, throw, throwThe, MonadExceptOf.throw] at hchk'
  | succ nb' =>
    have hnpi : ∀ a b bm, res' ≠ .forallE a b bm := by
      rintro a b bm rfl
      obtain ⟨a₀, b₀, rfl, -, -⟩ := hrr.forallE_inv
      simp [Expr.piArity] at hres0
    have hva : o.validAt self res' = true := checkCtorPos_valid hchk' hnpi
    simp only [Official.PosOracle.validAt, Bool.and_eq_true, beq_iff_eq] at hva
    obtain ⟨⟨⟨hfn', hlen'⟩, htake'⟩, hdrop'⟩ := hva
    obtain ⟨t, ty, ht, hfx, -, -, hargs⟩ := hrr.spine hσ hfn' |>.1 hself
    refine ⟨by simp [nestResHead, hfx], ?_⟩
    rw [List.all_eq_true]
    intro x hx
    have hpsl : o.ps.length = ctx.nP := by rw [hσ.ps, hσ.psEq, hσ.psLen]
    have h3 := Rel2.drop ctx.nP hargs
    have hq : ∀ y ∈ res'.getAppArgs.drop ctx.nP, o.occ y = false := by
      intro y hy
      rw [← hpsl] at hy
      have := List.all_eq_true.mp hdrop' y hy
      simpa using this
    have := Rel2.forall_left (P := fun a => a.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false)
      (fun a b hab hb => by
        cases hc : a.nestOcc ctx.names ctx.nP (ctx.hiAt 0)
        · rfl
        · have := hab.occ_of hσ (by simpa using hc)
          rw [this] at hb; exact nomatch hb) h3 hq x hx
    simp [this]

/-- **(A) ∘ (B) at a member constructor.**  Official accepting the
σ-constructor's positivity, under `WhnfSim` and the two recursion
obligations (`ContProv`, `SynProv`), with the non-positivity checks U4
and M3/M2′ of the derived telescope (`hside`), gives a derivation index
`n` such that the walk's run of the member constructor succeeds whenever
its input-derived fuel reaches `n`. -/
theorem nestMemberCtor_of_official (hσ : SigmaOk ctx σ o) (hsim : WhnfSim ops env ctx σ o.whnf)
    (hprov : ContProv ops env ctx σ o [] []) (hsyn : SynProv ops env ctx σ o [] [])
    {self : Name} (hself : ctx.names.contains self = true) {fuel nb nF : Nat} {crest ct' : Expr}
    (hrel : SRel ctx σ [] [] crest ct') (hpi : crest.piArity = nF)
    (hchk : Official.checkCtorPos o self fuel nb (ctx.hiAt 0) ct' = .ok ())
    (hside : ∀ n ks nds cur, PosDR ops env ctx n (.tele [] [] (ctx.hiAt 0) nF 0 crest ks nds cur) →
      ((List.range nF).any fun i => (ks.getD i .ordinary).guarded &&
        structUsedLater (closeTelescope nds (ctx.hiAt 0) cur) 0 i) = false ∧
      (closeTelescope nds (ctx.hiAt 0) cur).holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true) :
    ∃ n, ∀ st, RInv ctx st [] → n ≤ whnfWalkFuel crest →
      ∃ ks tyN st', nestMemberCtor ops env ctx nF crest st = .ok (ks, tyN, st') := by
  obtain ⟨n, ks, nds, cur, hd, hres, hidx⟩ := posA_member hσ hsim hprov hsyn hself hrel hpi hchk
  obtain ⟨hu4, hha⟩ := hside n ks nds cur hd
  refine ⟨n, fun st hI hfuel => ?_⟩
  obtain ⟨ks', st', h, -, -⟩ :=
    memberCtorDR_run (ctx := ctx) ⟨nds, cur, hd, rfl, hu4, hres, hidx, hha⟩ hfuel hI
  exact ⟨ks', _, st', h⟩

end Tele

end ConLeche
