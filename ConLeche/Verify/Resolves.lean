module

public import ConLeche.Verify.Denote
public import ConLeche.Verify.Close
public import ConLeche.IsModel
import ConLeche.Verify.Denote.Lemmas
import ConLeche.Verify.Shift
import ConLeche.Verify.Abstract

public section

/-!
# Terms every part of which reads

`Expr.Resolves env e`: every part of `e` is one the readings read — a constant stored at as many
levels as it has parameters, a projection with a stored table and an index in range, a literal
whose constants are stored, no free variable.  It is a property of the syntax alone: binders do
not ask anything of their domains, so a term resolves wherever its parts do, at every variable
environment.  Every reading of a resolving term succeeds (`Denotes_of_resolves`,
`ConLeche/Model/IsModelBridge.lean`).

The operations that build a recursor rule's ι equation out of stored terms keep it: lifting,
instantiating at resolving terms, level instantiation, application spines, telescopes.  And a
stored term the proofs' own reading `denote` reads resolves (`resolves_of_denote`).
-/

namespace ConLeche

/-- **Every part of the term reads in `env`**: see the module docstring. -/
@[expose] def Expr.Resolves (env : Env) : Expr → Prop
  | .bvar _ | .sort _ => True
  | .fvar _ _ => False
  | .const n us => ∃ ci, env.find? n = some ci ∧ us.length = ci.toConstantVal.levelParams.length
  | .app f a => f.Resolves env ∧ a.Resolves env
  | .lam ty b | .forallE ty b => ty.Resolves env ∧ b.Resolves env
  | .letE _ v b => v.Resolves env ∧ b.Resolves env
  | .proj T i e => (env.findProj? T i).isSome = true ∧ e.Resolves env
  | .lit (.natVal _) => natLitSupported env = true
  | .lit (.strVal _) => strLitSupported env = true

namespace Expr

variable {env : Env}

theorem resolves_liftLooseBVars (n : Nat) :
    ∀ (e : Expr) (c : Nat), (e.liftLooseBVars n c).Resolves env ↔ e.Resolves env := by
  intro e
  induction e with
  | bvar i => intro c; simp only [liftLooseBVars]; split <;> simp [Resolves]
  | lit l => intro c; cases l <;> rfl
  | _ => intro c; simp_all [liftLooseBVars, Resolves]

theorem resolves_instantiateLift {vs : List Expr} (hvs : ∀ v ∈ vs, v.Resolves env) :
    ∀ (e : Expr) (d : Nat), e.Resolves env → (e.instantiateLift vs d).Resolves env := by
  intro e
  induction e with
  | bvar j =>
    intro d _
    simp only [instantiateLift]
    split
    · trivial
    · split
      · exact (resolves_liftLooseBVars d _ 0).mpr (hvs _ (List.getElem_mem _))
      · trivial
  | lit l => intro d h; cases l <;> exact h
  | _ => intro d h; simp_all [instantiateLift, Resolves]

theorem resolves_instantiate1 {v : Expr} (hv : v.Resolves env) :
    ∀ (e : Expr) (d : Nat), e.Resolves env → (e.instantiate1 v d).Resolves env := by
  intro e
  induction e with
  | bvar j =>
    intro d _
    simp only [instantiate1]
    split
    · exact hv
    · split <;> trivial
  | lit l => intro d h; cases l <;> exact h
  | _ => intro d h; simp_all [instantiate1, Resolves]

theorem resolves_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ e : Expr, (e.instantiateLevelParams ks us).Resolves env ↔ e.Resolves env := by
  intro e
  induction e with
  | lit l => cases l <;> rfl
  | _ => simp_all [instantiateLevelParams, Resolves]

theorem resolves_mkAppN : ∀ (args : List Expr) (f : Expr),
    (mkAppN f args).Resolves env ↔ f.Resolves env ∧ ∀ a ∈ args, a.Resolves env
  | [], f => by simp [mkAppN]
  | a :: as, f => by
    rw [mkAppN, resolves_mkAppN as]
    simp only [Resolves, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨hf, ha⟩, has⟩; exact ⟨hf, ha, has⟩
    · rintro ⟨hf, ha, has⟩; exact ⟨⟨hf, ha⟩, has⟩

theorem resolves_getApp : ∀ (e : Expr), e.Resolves env →
    e.getAppFn.Resolves env ∧ ∀ a ∈ e.getAppArgs, a.Resolves env
  | .app f a, h => by
    obtain ⟨hf, ha⟩ := resolves_getApp f h.1
    refine ⟨hf, fun x hx => ?_⟩
    simp only [getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ha x hx
    · exact h.2
  | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .lam _ _, h | .forallE _ _, h
  | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => ⟨h, fun _ hx => nomatch hx⟩

theorem resolves_stripPis : ∀ (k : Nat) (e : Expr) {ds : List Expr} {b : Expr},
    e.stripPis k = some (ds, b) → e.Resolves env → (∀ x ∈ ds, x.Resolves env) ∧ b.Resolves env
  | 0, e, ds, b, h, he => by
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ hx => (nomatch hx), he⟩
  | k + 1, .forallE ty body, ds, b, h, he => by
    simp only [stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨ds', b'⟩, h', he'⟩ := h
    simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    obtain ⟨hds, hb⟩ := resolves_stripPis k body h' he.2
    refine ⟨fun x hx => ?_, hb⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact he.1
    · exact hds x hx
  | _ + 1, .bvar _, _, _, h, _ | _ + 1, .fvar _ _, _, _, h, _ | _ + 1, .sort _, _, _, h, _
  | _ + 1, .const _ _, _, _, h, _ | _ + 1, .app _ _, _, _, h, _ | _ + 1, .lam _ _, _, _, h, _
  | _ + 1, .letE _ _ _, _, _, h, _ | _ + 1, .lit _, _, _, h, _ | _ + 1, .proj _ _ _, _, _, h, _ =>
    nomatch h

theorem resolves_foldr_forallE : ∀ (ds : List Expr) (b : Expr),
    (ds.foldr .forallE b).Resolves env ↔ (∀ x ∈ ds, x.Resolves env) ∧ b.Resolves env
  | [], b => by simp
  | x :: ds, b => by
    simp only [List.foldr_cons, Resolves, resolves_foldr_forallE ds b, List.mem_cons,
      forall_eq_or_imp]
    constructor
    · rintro ⟨hx, hds, hb⟩; exact ⟨⟨hx, hds⟩, hb⟩
    · rintro ⟨⟨hx, hds⟩, hb⟩; exact ⟨hx, hds, hb⟩

theorem resolves_dropVars : ∀ (n : Nat) (e : Expr), e.Resolves env → (Expr.dropVars n e).Resolves env
  | 0, _, h => h
  | n + 1, e, h => resolves_dropVars n _ (resolves_instantiate1 (v := .sort .zero) trivial e 0 h)

end Expr

open Expr Verify Term in
/-- **What `denote` reads resolves**: the closure of a term `denote` reads at depth `d`. -/
theorem resolves_of_denote {acval : Name → (Name → Nat) → Term} {env : Env} {φ : Name → Nat} :
    ∀ (d : Nat) (e : Expr) {ta : Term},
      denote acval env φ d e = some ta →
      Expr.fvarsBelow d e → e.looseBVarsBounded 0 = true →
      (closeN d e).Resolves env := by
  intro d e
  induction d, e using denote.induct (env := env) with
  | case1 d u => intro _ _ _ _; trivial
  | case2 d idx ty => intro _ _ _ _; trivial
  | case3 d n us ci hf hlen => intro _ _ _ _; exact ⟨ci, hf, hlen⟩
  | case4 d n us ci hf hlen =>
    intro ta h
    rw [denote, hf] at h
    dsimp only at h
    rw [ite_eq_right hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro ta h
    rw [denote, hf] at h
    exact nomatch h
  | case6 d ty body ihty ihbody =>
    intro ta h hfb hlb
    obtain ⟨tA, bA, hta, hba, -⟩ := denote_forallE_inv h
    have hfb' : Expr.fvarsBelow d ty ∧ Expr.fvarsBelow d body := hfb
    have hlb' : (ty.looseBVarsBounded 0 && body.looseBVarsBounded 1) = true := hlb
    rw [Bool.and_eq_true] at hlb'
    show Resolves env (Expr.forallE (closeN d ty 0) (closeN d body 1))
    have hb := ihbody hba (Expr.fvarsBelow_instantiate1 0 hfb'.2)
      (ConLeche.looseBVarsBounded_instantiate1 body 0 hlb'.2)
    rw [Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2] at hb
    exact ⟨ihty hta hfb'.1 hlb'.1, hb⟩
  | case7 d ty body ihty ihbody =>
    intro ta h hfb hlb
    obtain ⟨tA, bA, hta, hba, -⟩ := denote_lam_inv h
    have hfb' : Expr.fvarsBelow d ty ∧ Expr.fvarsBelow d body := hfb
    have hlb' : (ty.looseBVarsBounded 0 && body.looseBVarsBounded 1) = true := hlb
    rw [Bool.and_eq_true] at hlb'
    show Resolves env (Expr.lam (closeN d ty 0) (closeN d body 1))
    have hb := ihbody hba (Expr.fvarsBelow_instantiate1 0 hfb'.2)
      (ConLeche.looseBVarsBounded_instantiate1 body 0 hlb'.2)
    rw [Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2] at hb
    exact ⟨ihty hta hfb'.1 hlb'.1, hb⟩
  | case8 d fe a ihf iha =>
    intro ta h hfb hlb
    obtain ⟨fA, aA, hfa, haa, -⟩ := denote_app_inv h
    have hfb' : Expr.fvarsBelow d fe ∧ Expr.fvarsBelow d a := hfb
    have hlb' : (fe.looseBVarsBounded 0 && a.looseBVarsBounded 0) = true := hlb
    rw [Bool.and_eq_true] at hlb'
    exact ⟨ihf hfa hfb'.1 hlb'.1, iha haa hfb'.2 hlb'.2⟩
  | case9 d ty val body ihty ihv ihbody =>
    intro ta h hfb hlb
    obtain ⟨-, va, ba, -, hva, hba, -⟩ := denote_letE_inv h
    have hfb' : Expr.fvarsBelow d ty ∧ Expr.fvarsBelow d val ∧
        Expr.fvarsBelow d body := hfb
    have hlb' : (ty.looseBVarsBounded 0 && val.looseBVarsBounded 0 &&
        body.looseBVarsBounded 1) = true := hlb
    simp only [Bool.and_eq_true] at hlb'
    show Resolves env (Expr.letE (closeN d ty 0) (closeN d val 0) (closeN d body 1))
    have hb := ihbody hba (Expr.fvarsBelow_instantiate1 0 hfb'.2.2)
      (ConLeche.looseBVarsBounded_instantiate1 body 0 hlb'.2)
    rw [Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2.2] at hb
    exact ⟨ihv hva hfb'.2.1 hlb'.1.2, hb⟩
  | case10 d sn i e ihe =>
    intro ta h hfb hlb
    obtain ⟨ia, entry, hia, hfp, -⟩ := denote_proj_inv h
    show Resolves env (Expr.proj sn i (closeN d e 0))
    exact ⟨by rw [hfp]; rfl, ihe hia hfb hlb⟩
  | case11 d k hsup => intro _ _ _ _; exact hsup
  | case12 d k hsup =>
    intro ta h
    rw [denote, ite_eq_right hsup] at h
    exact nomatch h
  | case13 d s hsup => intro _ _ _ _; exact hsup
  | case14 d s hsup =>
    intro ta h
    rw [denote, ite_eq_right hsup] at h
    exact nomatch h
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ta h
    cases x with
    | bvar i => rw [denote.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b => exact absurd rfl (hpi ty b)
    | lam ty b => exact absurd rfl (hlam ty b)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

open Verify Term in
/-- **A closed term `denote` reads resolves.** -/
theorem resolves_of_denote_closed {acval : Name → (Name → Nat) → Term} {env : Env}
    {φ : Name → Nat} {e : Expr} {ta : Term} (h : denote acval env φ 0 e = some ta)
    (hnf : e.hasFvar = false) (hlb : e.looseBVarsBounded 0 = true) : e.Resolves env := by
  have hr := resolves_of_denote 0 e h (fvarsBelow_zero hnf) hlb
  rwa [Expr.closeN_of_hasFvar e 0 0 hnf] at hr
where
  fvarsBelow_zero : ∀ {e : Expr}, e.hasFvar = false → Expr.fvarsBelow 0 e := by
    intro e
    induction e <;> simp_all [Expr.fvarsBelow, Expr.hasFvar]

/-- A telescope over an application determines its binders and the application. -/
theorem foldr_forallE_app_inj : ∀ {ds ds' : List Expr} {f a f' a' : Expr},
    ds.foldr Expr.forallE (Expr.app f a) = ds'.foldr Expr.forallE (Expr.app f' a') →
    ds = ds' ∧ f = f' ∧ a = a'
  | [], [], _, _, _, _, h => by
    simp only [List.foldr_nil, Expr.app.injEq] at h
    exact ⟨rfl, h⟩
  | d :: ds, d' :: ds', _, _, _, _, h => by
    simp only [List.foldr_cons, Expr.forallE.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h3, h4⟩ := foldr_forallE_app_inj h2
    exact ⟨by rw [h1, h3], h4⟩
  | [], _ :: _, _, _, _, _, h | _ :: _, [], _, _, _, _, h => by
    simp at h

/-- **A recursor rule's ι equation, in parts**: a telescope over `@Eq.{u} ty lhs rhs` whose
binders and three sides resolve where the equation's ingredients do — the recursor's and the
constructor's types, the rule's right-hand side and nested pins, the recursor at its own parameters
and the constructor at the rule's levels.  (`Eq` itself need not be stored.) -/
theorem iotaEqAt_parts {env : Env} {cvj : ConstantVal} {cnP : Nat} {cv : ConstantVal}
    {mI rP : Nat} {rl : RecRule} {e : Expr}
    (hcv : cv.type.Resolves env) (hcvj : cvj.type.Resolves env) (hrhs : rl.rhs.Resolves env)
    (hpins : ∀ lvls pins, rl.fire = .nested lvls pins → ∀ p ∈ pins, p.Resolves env)
    (hrec : ∃ ci, env.find? cv.name = some ci ∧
      cv.levelParams.length = ci.toConstantVal.levelParams.length)
    (hctor : ∃ ci, env.find? rl.ctor = some ci ∧
      (rl.ctorLevels cvj.levelParams).length = ci.toConstantVal.levelParams.length)
    (he : iotaEqAt cvj cnP cv mI rP rl = some e) :
    ∃ (ds : List Expr) (u : Level) (ty lhs rhs : Expr),
      e = ds.foldr .forallE (.app (.app (.app (.const eqName [u]) ty) lhs) rhs) ∧
      (∀ d ∈ ds, d.Resolves env) ∧ ty.Resolves env ∧ lhs.Resolves env ∧ rhs.Resolves env := by
  unfold iotaEqAt at he
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at he
  obtain ⟨⟨pre, rest⟩, hpre, he⟩ := he
  obtain ⟨⟨idx, body⟩, hbody, he⟩ := he
  obtain ⟨u, -, he⟩ := he
  obtain ⟨⟨pd, ctorBody⟩, hcb, he⟩ := he
  obtain ⟨⟨fd, concl⟩, hfd, he⟩ := he
  obtain ⟨_, hg, rfl⟩ := he
  simp only [guard] at hg
  split at hg
  case isFalse => exact nomatch hg
  -- the pieces
  have hbv : ∀ (l : List Nat) (f : Nat → Nat), ∀ x ∈ l.map (fun i => Expr.bvar (f i)),
      x.Resolves env := by
    intro l f x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    trivial
  obtain ⟨hpreR, hrestR⟩ := Expr.resolves_stripPis _ _ hpre hcv
  obtain ⟨-, hbodyR⟩ := Expr.resolves_stripPis _ _ hbody hrestR
  obtain ⟨-, hcbR⟩ := Expr.resolves_stripPis _ _ hcb
    ((Expr.resolves_instantiateLevelParams _ _ _).mpr hcvj)
  have hparams : ∀ p ∈ rl.iotaParams rP cnP, p.Resolves env := by
    unfold RecRule.iotaParams
    split
    · next lvls pins hf => exact hpins lvls pins hf
    · exact hbv _ _
  obtain ⟨hfdR, hconclR⟩ := Expr.resolves_stripPis _ _ hfd
    (Expr.resolves_instantiateLift (fun v hv => hparams v (List.mem_reverse.mp hv)) ctorBody 0
      hcbR)
  obtain ⟨-, hargs⟩ := Expr.resolves_getApp concl hconclR
  have hidx : ∀ x ∈ concl.getAppArgs.drop cnP, x.Resolves env :=
    fun x hx => hargs x (List.mem_of_mem_drop hx)
  have hmajor : (Expr.mkAppN (.const rl.ctor (rl.ctorLevels cvj.levelParams))
      ((rl.iotaParams rP cnP).map (·.liftLooseBVars rl.nfields 0) ++
        (List.range rl.nfields).map fun j => Expr.bvar (rl.nfields - 1 - j))).Resolves env := by
    refine (Expr.resolves_mkAppN _ _).mpr ⟨hctor, fun a ha => ?_⟩
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      exact (Expr.resolves_liftLooseBVars _ _ _).mpr (hparams p hp)
    · exact hbv _ _ a ha
  refine ⟨pre ++ fd, u, _, _, _, rfl,
    fun x hx => (List.mem_append.mp hx).elim (hpreR x) (hfdR x), ?_, ?_, ?_⟩
  · refine Expr.resolves_instantiateLift (fun v hv => ?_) _ 0
      ((Expr.resolves_liftLooseBVars _ _ _).mpr hbodyR)
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hmajor
    · exact hidx v (List.mem_reverse.mp hv)
  · refine (Expr.resolves_mkAppN _ _).mpr ⟨?_, fun a ha => ?_⟩
    · obtain ⟨ci, hf, hl⟩ := hrec
      exact ⟨ci, hf, by rw [List.length_map]; exact hl⟩
    · rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · exact hbv _ _ a ha
        · exact hidx a ha
      · rw [List.mem_singleton.mp ha]; exact hmajor
  · refine (Expr.resolves_mkAppN _ _).mpr ⟨hrhs, fun a ha => ?_⟩
    rcases List.mem_append.mp ha with ha | ha <;> exact hbv _ _ a ha

end ConLeche
