module

public import ConLeche.Verify.Inductives.PosComplete
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Subst
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Verify.Cached.Erase

public section

/-!
# Official's positivity ⇒ the walk never rejects: the run-level form of (A) (lane COMPLETE-3)

COMPLETE-2 stated half (A) as "official accepts ⇒ a `PosDR` derivation
exists".  That form needs the recursion into container frames to
TERMINATE, and the walk's keys (hole representations) are not injective
into official's finite auxiliary set, so no simple measure is available.

This module states (A) at the RUN, at EVERY fuel: official accepting
makes `nestPos`/`nestSyn` succeed or DECLINE (a resource limit — the
walk's own fuel, a level comparison's), never reject
(`OkOr`).  The proof is an induction on the walk's own fuel — every
recursive call the walk makes is one fuel lower — so no measure on the
frame recursion is needed.  It is also the form the arena needs: the
kernel runs the walk at a FIXED fuel (`whnfWalkFuel`), where a
derivation's index says nothing, while "no reject at any fuel" says the
walk's only divergence from official is a decline.

The frames' obligations (what official's acceptance supplies at a fresh
instantiation: its container, its former's checks, its constructors
related to official's auxiliary constructors, the checks that are not
positivity) are collected in `Steps`, to be discharged separately (the
frame-constructor relation, the elimination link, the side checks).
-/

namespace ConLeche

open Expr

/-! ## Accept-or-decline -/

/-- **A decline**: a resource limit, never a verdict. -/
@[expose] def Decline (e : CheckError) : Prop := ∃ w, e = .notImplemented w

/-- **The run succeeds (with `P`) or declines** — it never rejects. -/
@[expose] def OkOr {α : Type} (P : α → Prop) : CheckM α → Prop
  | .ok a => P a
  | .error e => Decline e

theorem OkOr.bind {α β : Type} {P : α → Prop} {Q : β → Prop} {r : CheckM α}
    {g : α → CheckM β} (h : OkOr P r) (hg : ∀ a, P a → OkOr Q (g a)) :
    OkOr Q (r >>= g) := by
  cases r with
  | ok a => exact hg a h
  | error e => exact h

theorem OkOr.mono {α : Type} {P Q : α → Prop} {r : CheckM α} (h : OkOr P r)
    (hPQ : ∀ a, P a → Q a) : OkOr Q r := by
  cases r with
  | ok a => exact hPQ a h
  | error e => exact h

theorem OkOr.of_ok {α : Type} {P : α → Prop} {r : CheckM α} {a : α} (h : r = .ok a)
    (hp : P a) : OkOr P r := by
  subst h; exact hp

theorem OkOr.bind_eq {α β : Type} {P : α → Prop} {Q : β → Prop} {r : CheckM α}
    {g : α → CheckM β} (h : OkOr P r) (hg : ∀ a, r = .ok a → P a → OkOr Q (g a)) :
    OkOr Q (r >>= g) := by
  cases hr : r with
  | ok a => rw [hr] at h; exact hg a hr h
  | error e => rw [hr] at h; exact h

theorem OkOr.ok_bind {α β : Type} {Q : β → Prop} {a : α} {g : α → CheckM β}
    (h : OkOr Q (g a)) : OkOr Q ((Except.ok a : CheckM α) >>= g) := h

theorem OkOr.fuel {α : Type} {P : α → Prop} (w : String) :
    OkOr P (throw (.notImplemented w) : CheckM α) := ⟨w, rfl⟩

/-! ## Official's replacement is complete on σ-terms -/

/-- **Official's nested application** (`is_nested_inductive_app` at the
σ-world, read against the walk's environment): a stored inductive `C`
(not a member, not `Quot`) with at least its parameters, some parameter
mentioning a declared type. -/
@[expose] def NestedSig (ctx : NestCtx) (o : Official.PosOracle) (s : Expr) : Prop :=
  ∃ C us caps cv, s.getAppFn = .const C us ∧ ctx.names.contains C = false ∧ C ≠ quotName ∧
    ctx.find? C = some (.indInfo cv caps) ∧ caps.nparams ≤ s.getAppArgs.length ∧
    (s.getAppArgs.take caps.nparams).any o.occ = true

/-- **A σ-term official's replacement has passed over**: every nested
application was replaced by its auxiliary type (whose arguments —
parameters and raw indices — are not read further), member applications
and everything else are traversed. -/
inductive SigNF (ctx : NestCtx) (o : Official.PosOracle) (isAux : Name → Bool) : Expr → Prop where
  | aux {a : Name} {us : List Level} {args : List Expr} (ha : isAux a = true) :
      SigNF ctx o isAux (Expr.mkAppN (.const a us) args)
  | mem {n : Name} {us : List Level} {args : List Expr} (hn : ctx.names.contains n = true)
      (hargs : ∀ x ∈ args, SigNF ctx o isAux x) :
      SigNF ctx o isAux (Expr.mkAppN (.const n us) args)
  | app {f a : Expr} (hns : ¬ NestedSig ctx o (.app f a))
      (hf : SigNF ctx o isAux f) (ha : SigNF ctx o isAux a) : SigNF ctx o isAux (.app f a)
  | lam {t b : Expr} {m : BinderMeta} : SigNF ctx o isAux t → SigNF ctx o isAux b →
      SigNF ctx o isAux (.lam t b m)
  | forallE {t b : Expr} {m : BinderMeta} : SigNF ctx o isAux t → SigNF ctx o isAux b →
      SigNF ctx o isAux (.forallE t b m)
  | letE {t v b : Expr} : SigNF ctx o isAux t → SigNF ctx o isAux v → SigNF ctx o isAux b →
      SigNF ctx o isAux (.letE t v b)
  | proj {s : Name} {i : Nat} {x : Expr} : SigNF ctx o isAux x → SigNF ctx o isAux (.proj s i x)
  | bvar (i : Nat) : SigNF ctx o isAux (.bvar i)
  | fvar (i : Nat) (ty : Expr) : SigNF ctx o isAux (.fvar i ty)
  | sort (u : Level) : SigNF ctx o isAux (.sort u)
  | lit (l : Literal) : SigNF ctx o isAux (.lit l)
  | const (n : Name) (us : List Level) : SigNF ctx o isAux (.const n us)

section Syn

variable {ctx : NestCtx} {σ : SigmaCtx} {o : Official.PosOracle} {prog : List NestHole}
  {act : List NestKey}

theorem getAppFn_ne_const_of {x : Expr} {n : Name} {us : List Level} {args : List Expr}
    (h : Expr.mkAppN (.const n us) args = x) (hx : ∀ n' us', x.getAppFn ≠ .const n' us') : False := by
  have := congrArg Expr.getAppFn h
  rw [Expr.getAppFn_mkAppN] at this
  exact hx n us this.symm

/-- **The walk-side spine inversion**: a walk term headed by a stored
constant is a fresh container instantiation (its auxiliary type on the
σ-side) applied further, or a congruence (the σ-term headed by the same
constant, not a declared type). -/
theorem SRel.spine_const {x x' : Expr} (h : SRel ctx σ prog act x x') :
    ∀ {C : Name} {us : List Level}, x.getAppFn = .const C us →
      (∃ ds is is' a, σ.contAux prog ⟨C, us, ds⟩ = some a ∧ ContKeyOk ctx σ.isAux prog act C us ds ∧
        x = Expr.mkAppN (Expr.mkAppN (.const C us) ds) is ∧
        x' = Expr.mkAppN (Expr.mkAppN (.const a σ.lvls) σ.ps) is' ∧
        Rel2 (SRel ctx σ prog act) is is') ∨
      (x'.getAppFn = .const C us ∧ ctx.names.contains C = false ∧ σ.isAux C = false ∧
        Rel2 (SRel ctx σ prog act) x.getAppArgs x'.getAppArgs) := by
  induction h with
  | mem _ => intro C us hfn; simp [Expr.getAppFn] at hfn
  | frm _ _ _ =>
    intro C us hfn
    rw [Expr.getAppFn_mkAppN] at hfn
    simp [Expr.getAppFn] at hfn
  | @cnt C' us' ds a ha hk =>
    intro C us hfn
    rw [Expr.getAppFn_mkAppN] at hfn
    simp only [Expr.getAppFn, Expr.const.injEq] at hfn
    obtain ⟨rfl, rfl⟩ := hfn
    exact .inl ⟨ds, [], [], a, ha, hk, rfl, rfl, .nil⟩
  | const hn ha =>
    intro C us hfn
    simp only [Expr.getAppFn, Expr.const.injEq] at hfn
    obtain ⟨rfl, rfl⟩ := hfn
    exact .inr ⟨rfl, hn, ha, by simpa [Expr.getAppArgs] using Rel2.nil⟩
  | @app f a f' a' _ ha ihf _ =>
    intro C us hfn
    simp only [Expr.getAppFn] at hfn
    rcases ihf hfn with ⟨ds, is, is', a₀, hca, hok, rfl, rfl, hr⟩ | ⟨hfn', hn, hax, hr⟩
    · exact .inl ⟨ds, is ++ [a], is' ++ [a'], a₀, hca, hok, by rw [Expr.mkAppN_append_one],
        by rw [Expr.mkAppN_append_one], Rel2.append hr (.cons ha .nil)⟩
    · refine .inr ⟨by simpa [Expr.getAppFn] using hfn', hn, hax, ?_⟩
      simp only [Expr.getAppArgs]
      exact Rel2.append hr (.cons ha .nil)
  | raw _ _ _ _ _ _ =>
    intro C us hfn
    rw [Expr.getAppFn_mkAppN] at hfn
    simp [Expr.getAppFn] at hfn
  | _ => intro C us hfn; simp [Expr.getAppFn] at hfn

theorem SigNF.not_nested {isAux : Name → Bool}
    (hauxEnv : ∀ a, isAux a = true → ∀ cv caps, ctx.find? a ≠ some (.indInfo cv caps))
    {e : Expr} (h : SigNF ctx o isAux e) (hn : NestedSig ctx o e) : False := by
  obtain ⟨C, us, caps, cv, hfn, hnm, hq, hfind, hle, hany⟩ := hn
  cases h with
  | @aux a us' args ha =>
    rw [Expr.getAppFn_mkAppN] at hfn
    simp only [Expr.getAppFn, Expr.const.injEq] at hfn
    obtain ⟨rfl, rfl⟩ := hfn
    exact hauxEnv _ ha _ _ hfind
  | @mem n us' args hn' _ =>
    rw [Expr.getAppFn_mkAppN] at hfn
    simp only [Expr.getAppFn, Expr.const.injEq] at hfn
    obtain ⟨rfl, rfl⟩ := hfn
    rw [hn'] at hnm; exact nomatch hnm
  | app hns _ _ => exact hns ⟨C, us, caps, cv, hfn, hnm, hq, hfind, hle, hany⟩
  | const n us' => simp [Expr.getAppArgs] at hany
  | _ => simp [Expr.getAppFn] at hfn

theorem nestSynApp?_inv {hi : Nat} {e : Expr} {k : NestKey} (h : nestSynApp? ctx hi e = some k) :
    ∃ n us caps cv, e.getAppFn = .const n us ∧ ctx.names.contains n = false ∧ n ≠ quotName ∧
      ctx.find? n = some (.indInfo cv caps) ∧ caps.nparams ≤ e.getAppArgs.length ∧
      (e.getAppArgs.take caps.nparams).any (·.nestOcc ctx.names ctx.nP hi) = true ∧
      k = ⟨n, us, e.getAppArgs.take caps.nparams⟩ := by
  unfold nestSynApp? at h
  split at h
  · rename_i n us hfn
    split at h
    · exact nomatch h
    · rename_i hnq
      simp only [Bool.or_eq_true, not_or, beq_iff_eq] at hnq
      split at h
      · rename_i cv caps hf
        dsimp only at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          simp only [Option.some.injEq] at h
          exact ⟨n, us, caps, cv, hfn, by simpa using hnq.1, hnq.2, hf, hc.1, hc.2, h.symm⟩
        · exact nomatch h
      · exact nomatch h
  · exact nomatch h

theorem nestSynApp?_of {hi : Nat} {e : Expr} {n : Name} {us : List Level} {caps : IndCaps}
    {cv : ConstantVal} (hfn : e.getAppFn = .const n us) (hnm : ctx.names.contains n = false)
    (hq : n ≠ quotName) (hf : ctx.find? n = some (.indInfo cv caps))
    (hle : caps.nparams ≤ e.getAppArgs.length)
    (hocc : (e.getAppArgs.take caps.nparams).any (·.nestOcc ctx.names ctx.nP hi) = true) :
    nestSynApp? ctx hi e = some ⟨n, us, e.getAppArgs.take caps.nparams⟩ := by
  unfold nestSynApp?
  rw [hfn]
  simp only
  rw [if_neg (by
    simp only [Bool.or_eq_true, beq_iff_eq, not_or]
    exact ⟨by simpa using hnm, hq⟩)]
  rw [hf]
  simp only
  rw [if_pos (by simp [hle, hocc])]

/-- The auxiliary maps name stored inductives at their parameter count
(official's keys are `I (args.take nparams)`), and no auxiliary type is
stored. -/
structure AuxEnvOk (ctx : NestCtx) (σ : SigmaCtx) : Prop where
  notStored : ∀ a, σ.isAux a = true → ∀ cv caps, ctx.find? a ≠ some (.indInfo cv caps)
  cont : ∀ prog K a, σ.contAux prog K = some a →
    ∃ cv caps, ctx.find? K.cname = some (.indInfo cv caps) ∧ caps.nparams = K.ds.length

/-- A fresh container instantiation is a syntactic occurrence at its key. -/
theorem nestSynApp?_cnt (hae : AuxEnvOk ctx σ) {C : Name} {us : List Level}
    {ds is : List Expr} {a : Name} (hca : σ.contAux prog ⟨C, us, ds⟩ = some a)
    (hok : ContKeyOk ctx σ.isAux prog act C us ds) :
    nestSynApp? ctx (ctx.hiAt prog.length) (Expr.mkAppN (Expr.mkAppN (.const C us) ds) is)
      = some ⟨C, us, ds⟩ := by
  obtain ⟨cv, caps, hf, hnp⟩ := hae.cont _ _ _ hca
  have hargs : (Expr.mkAppN (Expr.mkAppN (.const C us) ds) is).getAppArgs = ds ++ is := by
    rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN]; simp [Expr.getAppArgs]
  have htake : (ds ++ is).take caps.nparams = ds := by
    simp only at hnp; rw [hnp]; simp
  have := nestSynApp?_of (ctx := ctx) (hi := ctx.hiAt prog.length)
    (e := Expr.mkAppN (Expr.mkAppN (.const C us) ds) is) (n := C) (us := us) (caps := caps)
    (cv := cv) (by rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN]; rfl) hok.1 hok.2.1 hf
    (by rw [hargs]; simp only at hnp; simp [hnp])
    (by
      rw [hargs, htake, List.any_eq_true]
      obtain ⟨x, hx, hxo⟩ := hok.2.2.2.2.1
      exact ⟨x, hx, hxo⟩)
  rw [hargs, htake] at this
  exact this

/-- At an application the scan descends into (no key there, not a frame
hole's), the relation and the normal form descend too. -/
theorem SRel.desc_app (hσ : SigmaOk ctx σ o) (hae : AuxEnvOk ctx σ) {f a e' : Expr}
    (hrel : SRel ctx σ prog act (.app f a) e') (hnf : SigNF ctx o σ.isAux e')
    (hnone : nestSynApp? ctx (ctx.hiAt prog.length) (.app f a) = none)
    (hnfr : ∀ i ty, (Expr.app f a).getAppFn = .fvar i ty →
      ¬ (ctx.hiAt 0 ≤ i ∧ i < ctx.hiAt prog.length)) :
    ∃ f' a', e' = .app f' a' ∧ SRel ctx σ prog act f f' ∧ SRel ctx σ prog act a a' ∧
      SigNF ctx o σ.isAux f' ∧ SigNF ctx o σ.isAux a' := by
  -- the walk side's base forms are excluded
  have hbase : ∀ x, SRel ctx σ prog act x e' → x = .app f a →
      ∃ f' a', e' = .app f' a' ∧ SRel ctx σ prog act f f' ∧ SRel ctx σ prog act a a' := by
    intro x hx hxe
    cases hx with
    | @frm i ty h a₀ hk _ _ =>
      exfalso
      have hi : i < prog.length := by
        have := (List.getElem?_eq_some_iff.mp hk).1
        simpa using this
      have := congrArg Expr.getAppFn hxe
      rw [Expr.getAppFn_mkAppN] at this
      exact hnfr _ _ this.symm ⟨by simp [NestCtx.hiAt], by simp [NestCtx.hiAt]; omega⟩
    | @cnt C us ds a₀ hca hok =>
      exfalso
      have := nestSynApp?_cnt (is := []) hae hca hok
      simp only [Expr.mkAppN] at this
      rw [hxe, hnone] at this
      exact nomatch this
    | app hf ha =>
      simp only [Expr.app.injEq] at hxe
      obtain ⟨rfl, rfl⟩ := hxe
      exact ⟨_, _, rfl, hf, ha⟩
    | @raw i ty h hk _ _ _ _ _ =>
      exfalso
      have hi : i < prog.length := by
        have := (List.getElem?_eq_some_iff.mp hk).1
        simpa using this
      have := congrArg Expr.getAppFn hxe
      rw [Expr.getAppFn_mkAppN] at this
      exact hnfr _ _ this.symm ⟨by simp [NestCtx.hiAt], by simp [NestCtx.hiAt]; omega⟩
    | _ => simp at hxe
  obtain ⟨f', a', rfl, hf, ha⟩ := hbase _ hrel rfl
  refine ⟨f', a', rfl, hf, ha, ?_⟩
  -- the σ-side's replaced form is excluded
  generalize he : Expr.app f' a' = e0 at hnf hrel
  cases hnf with
  | app _ hf' ha' =>
    simp only [Expr.app.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨hf', ha'⟩
  | @aux x us args hx =>
    exfalso
    have hfn : (Expr.mkAppN (.const x us) args).getAppFn = .const x us := by
      rw [Expr.getAppFn_mkAppN]; rfl
    obtain ⟨-, is, is', -, -, hcase⟩ := (hrel.spine hσ hfn).2 hx
    rcases hcase with ⟨i, ty, hk, hk', -, -, hxe⟩ | ⟨C, us', ds, hca, hok, hxe⟩
    · have hi : i < prog.length := by
        have := (List.getElem?_eq_some_iff.mp hk').1
        simpa using this
      have := congrArg Expr.getAppFn hxe
      rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN] at this
      exact hnfr _ _ this ⟨by simp [NestCtx.hiAt], by simp [NestCtx.hiAt]; omega⟩
    · have := nestSynApp?_cnt (is := is) hae hca hok
      rw [← hxe, hnone] at this
      exact nomatch this
  | @mem n us args hn hargs =>
    obtain ⟨args₀, a₀, rfl⟩ : ∃ args₀ a₀, args = args₀ ++ [a₀] := by
      rcases List.eq_nil_or_concat args with rfl | ⟨args₀, a₀, rfl⟩
      · simp [Expr.mkAppN] at he
      · exact ⟨args₀, a₀, List.concat_eq_append ..⟩
    rw [Expr.mkAppN_append_one] at he
    simp only [Expr.app.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨.mem hn (fun y hy => hargs y (List.mem_append_left _ hy)),
      hargs _ (List.mem_append_right _ (List.mem_singleton_self _))⟩
  | _ => simp at he

theorem mkAppN_const_ne {n : Name} {us : List Level} {args : List Expr} {x : Expr}
    (hx : ∀ n' us', x.getAppFn ≠ .const n' us') (h : Expr.mkAppN (.const n us) args = x) : False :=
  getAppFn_ne_const_of h hx

/-- Inversions at the binders and projections (the base cases are applications or
variables). -/
theorem SRel.lam_inv {t b e' : Expr} {m : BinderMeta} (h : SRel ctx σ prog act (.lam t b m) e') :
    ∃ t' b', e' = .lam t' b' m ∧ SRel ctx σ prog act t t' ∧ SRel ctx σ prog act b b' := by
  generalize hx : Expr.lam t b m = x at h
  cases h with
  | lam ht hb =>
    simp only [Expr.lam.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨_, _, rfl, ht, hb⟩
  | frm _ _ _ =>
    have := congrArg Expr.getAppFn hx; rw [Expr.getAppFn_mkAppN] at this; simp [Expr.getAppFn] at this
  | raw _ _ _ _ _ _ =>
    have := congrArg Expr.getAppFn hx; rw [Expr.getAppFn_mkAppN] at this; simp [Expr.getAppFn] at this
  | cnt _ _ =>
    have := congrArg Expr.getAppFn hx; rw [Expr.getAppFn_mkAppN] at this; simp [Expr.getAppFn] at this
  | _ => simp at hx

theorem SRel.letE_inv {t v b e' : Expr} (h : SRel ctx σ prog act (.letE t v b) e') :
    ∃ t' v' b', e' = .letE t' v' b' ∧ SRel ctx σ prog act t t' ∧ SRel ctx σ prog act v v' ∧
      SRel ctx σ prog act b b' := by
  generalize hx : Expr.letE t v b = x at h
  cases h with
  | letE ht hv hb =>
    simp only [Expr.letE.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨_, _, _, rfl, ht, hv, hb⟩
  | frm _ _ _ =>
    have := congrArg Expr.getAppFn hx; rw [Expr.getAppFn_mkAppN] at this; simp [Expr.getAppFn] at this
  | raw _ _ _ _ _ _ =>
    have := congrArg Expr.getAppFn hx; rw [Expr.getAppFn_mkAppN] at this; simp [Expr.getAppFn] at this
  | cnt _ _ =>
    have := congrArg Expr.getAppFn hx; rw [Expr.getAppFn_mkAppN] at this; simp [Expr.getAppFn] at this
  | _ => simp at hx

theorem SRel.proj_inv {sn : Name} {i : Nat} {x e' : Expr} (h : SRel ctx σ prog act (.proj sn i x) e') :
    ∃ x', e' = .proj sn i x' ∧ SRel ctx σ prog act x x' := by
  generalize hx : Expr.proj sn i x = y at h
  cases h with
  | proj hx' =>
    simp only [Expr.proj.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨_, rfl, hx'⟩
  | frm _ _ _ =>
    have := congrArg Expr.getAppFn hx; rw [Expr.getAppFn_mkAppN] at this; simp [Expr.getAppFn] at this
  | raw _ _ _ _ _ _ =>
    have := congrArg Expr.getAppFn hx; rw [Expr.getAppFn_mkAppN] at this; simp [Expr.getAppFn] at this
  | cnt _ _ =>
    have := congrArg Expr.getAppFn hx; rw [Expr.getAppFn_mkAppN] at this; simp [Expr.getAppFn] at this
  | _ => simp at hx

theorem SigNF.lam_inv {isAux : Name → Bool} {t b : Expr} {m : BinderMeta}
    (h : SigNF ctx o isAux (.lam t b m)) : SigNF ctx o isAux t ∧ SigNF ctx o isAux b := by
  generalize hx : Expr.lam t b m = x at h
  cases h with
  | lam ht hb =>
    simp only [Expr.lam.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨ht, hb⟩
  | aux _ => exact (mkAppN_const_ne (by rw [← hx]; simp [Expr.getAppFn]) rfl).elim
  | mem _ _ => exact (mkAppN_const_ne (by rw [← hx]; simp [Expr.getAppFn]) rfl).elim
  | _ => simp at hx

theorem SigNF.forallE_inv {isAux : Name → Bool} {t b : Expr} {m : BinderMeta}
    (h : SigNF ctx o isAux (.forallE t b m)) : SigNF ctx o isAux t ∧ SigNF ctx o isAux b := by
  generalize hx : Expr.forallE t b m = x at h
  cases h with
  | forallE ht hb =>
    simp only [Expr.forallE.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨ht, hb⟩
  | aux _ => exact (mkAppN_const_ne (by rw [← hx]; simp [Expr.getAppFn]) rfl).elim
  | mem _ _ => exact (mkAppN_const_ne (by rw [← hx]; simp [Expr.getAppFn]) rfl).elim
  | _ => simp at hx

theorem SigNF.letE_inv {isAux : Name → Bool} {t v b : Expr}
    (h : SigNF ctx o isAux (.letE t v b)) :
    SigNF ctx o isAux t ∧ SigNF ctx o isAux v ∧ SigNF ctx o isAux b := by
  generalize hx : Expr.letE t v b = x at h
  cases h with
  | letE ht hv hb =>
    simp only [Expr.letE.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨ht, hv, hb⟩
  | aux _ => exact (mkAppN_const_ne (by rw [← hx]; simp [Expr.getAppFn]) rfl).elim
  | mem _ _ => exact (mkAppN_const_ne (by rw [← hx]; simp [Expr.getAppFn]) rfl).elim
  | _ => simp at hx

theorem SigNF.proj_inv {isAux : Name → Bool} {sn : Name} {i : Nat} {x : Expr}
    (h : SigNF ctx o isAux (.proj sn i x)) : SigNF ctx o isAux x := by
  generalize hx : Expr.proj sn i x = y at h
  cases h with
  | proj hx' =>
    simp only [Expr.proj.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact hx'
  | aux _ => exact (mkAppN_const_ne (by rw [← hx]; simp [Expr.getAppFn]) rfl).elim
  | mem _ _ => exact (mkAppN_const_ne (by rw [← hx]; simp [Expr.getAppFn]) rfl).elim
  | _ => simp at hx

/-- **Every key of the syntactic scan is a fresh container instantiation
official replaced** (its auxiliary type the σ-side's): the scan and
official's `replace_all_nested` read the same occurrences. -/
theorem nestSynGo_keys (hσ : SigmaOk ctx σ o) (hae : AuxEnvOk ctx σ) :
    ∀ (e e' : Expr) (acc : NestSynAcc), SRel ctx σ prog act e e' → SigNF ctx o σ.isAux e' →
      ∀ k ∈ (nestSynGo ctx (ctx.hiAt prog.length) e acc).keys.toList,
        k ∈ acc.keys.toList ∨
          ∃ a, σ.contAux prog k = some a ∧ ContKeyOk ctx σ.isAux prog act k.cname k.lvls k.ds := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro e' acc hrel hnf k hk
    rw [nestSynGo] at hk
    split at hk
    · exact .inl hk
    · dsimp only at hk
      split at hk
      · rename_i k' hk'
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hk
        rcases hk with hk | rfl
        · exact .inl hk
        · right
          obtain ⟨n, us, caps, cv, hfn, hnm, hq, hf, hle, hocc, rfl⟩ := nestSynApp?_inv hk'
          rcases hrel.spine_const hfn with ⟨ds, is, is', a₀, hca, hok, hx, -, -⟩ |
            ⟨hfn', -, -, hr⟩
          · have := nestSynApp?_cnt (is := is) hae hca hok
            rw [← hx, hk'] at this
            simp only [Option.some.injEq] at this
            rw [this]
            exact ⟨a₀, hca, hok⟩
          · exfalso
            refine hnf.not_nested hae.notStored ⟨n, us, caps, cv, hfn', hnm, hq, hf,
              by rw [← hr.length_eq]; exact hle, ?_⟩
            have h3 := Rel2.take caps.nparams hr
            obtain ⟨x, hx, hxo⟩ := List.any_eq_true.mp hocc
            -- the related parameter carries a σ-occurrence
            have key : ∀ (xs xs' : List Expr), Rel2 (SRel ctx σ prog act) xs xs' →
                ∀ x ∈ xs, x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true →
                  xs'.any o.occ = true := by
              intro xs xs' hr' x hx hxo
              induction hr' with
              | nil => exact nomatch hx
              | cons h₁ _ ih =>
                rcases List.mem_cons.mp hx with rfl | hx
                · simp [h₁.occ_of hσ hxo]
                · simp [ih hx]
            exact key _ _ h3 x hx hxo
      · have lift : ∀ acc', (k ∈ acc'.keys.toList → k ∈ acc.keys.toList) →
            ∀ f' a', SRel ctx σ prog act f f' → SRel ctx σ prog act a a' →
            SigNF ctx o σ.isAux f' → SigNF ctx o σ.isAux a' →
            k ∈ (nestSynGo ctx (ctx.hiAt prog.length) a
              (nestSynGo ctx (ctx.hiAt prog.length) f acc')).keys.toList →
            k ∈ acc.keys.toList ∨
              ∃ a, σ.contAux prog k = some a ∧ ContKeyOk ctx σ.isAux prog act k.cname k.lvls k.ds := by
          intro acc' h0 f' a' hf ha hf' ha' hk
          rcases iha a' _ ha ha' k hk with hk | hk
          · rcases ihf f' _ hf hf' k hk with hk | hk
            · exact .inl (h0 hk)
            · exact .inr hk
          · exact .inr hk
        rename_i hnone
        split at hk
        · rename_i i ty hfn
          split at hk
          · exact .inl hk
          · rename_i hnfr
            obtain ⟨f', a', rfl, hf, ha, hf', ha'⟩ := hrel.desc_app hσ hae hnf hnone
              (fun i' ty' hfn' h' => by
                rw [hfn] at hfn'
                simp only [Expr.fvar.injEq] at hfn'
                obtain ⟨rfl, rfl⟩ := hfn'
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hnfr
                exact hnfr h')
            exact lift { acc with seen := acc.seen.insert (.app f a) } id f' a' hf ha hf' ha' hk
        · rename_i hnfv
          obtain ⟨f', a', rfl, hf, ha, hf', ha'⟩ := hrel.desc_app hσ hae hnf hnone
            (fun i' ty' hfn' _ => hnfv i' ty' hfn')
          exact lift { acc with seen := acc.seen.insert (.app f a) } id f' a' hf ha hf' ha' hk
  | lam t b bm iht ihb =>
    intro e' acc hrel hnf k hk
    rw [nestSynGo] at hk
    split at hk
    · exact .inl hk
    · obtain ⟨t', b', rfl, ht, hb⟩ := hrel.lam_inv
      obtain ⟨ht', hb'⟩ := hnf.lam_inv
      rcases ihb b' _ hb hb' k hk with hk | hk
      · rcases iht t' _ ht ht' k hk with hk | hk
        · exact .inl hk
        · exact .inr hk
      · exact .inr hk
  | forallE t b bm iht ihb =>
    intro e' acc hrel hnf k hk
    rw [nestSynGo] at hk
    split at hk
    · exact .inl hk
    · obtain ⟨t', b', rfl, ht, hb⟩ := hrel.forallE_inv_left
      obtain ⟨ht', hb'⟩ := hnf.forallE_inv
      rcases ihb b' _ hb hb' k hk with hk | hk
      · rcases iht t' _ ht ht' k hk with hk | hk
        · exact .inl hk
        · exact .inr hk
      · exact .inr hk
  | letE t v b iht ihv ihb =>
    intro e' acc hrel hnf k hk
    rw [nestSynGo] at hk
    split at hk
    · exact .inl hk
    · obtain ⟨t', v', b', rfl, ht, hv, hb⟩ := hrel.letE_inv
      obtain ⟨ht', hv', hb'⟩ := hnf.letE_inv
      rcases ihb b' _ hb hb' k hk with hk | hk
      · rcases ihv v' _ hv hv' k hk with hk | hk
        · rcases iht t' _ ht ht' k hk with hk | hk
          · exact .inl hk
          · exact .inr hk
        · exact .inr hk
      · exact .inr hk
  | proj sn i x ih =>
    intro e' acc hrel hnf k hk
    rw [nestSynGo] at hk
    split at hk
    · exact .inl hk
    · obtain ⟨x', rfl, hx⟩ := hrel.proj_inv
      rcases ih x' _ hx hnf.proj_inv k hk with hk | hk
      · exact .inl hk
      · exact .inr hk
  | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ =>
    intro e' acc _ _ k hk
    rw [nestSynGo] at hk
    split at hk <;> exact .inl hk

/-- The scan's keys, every one fresh and official's. -/
theorem nestSynOccs_keys (hσ : SigmaOk ctx σ o) (hae : AuxEnvOk ctx σ) {e e' : Expr}
    (hrel : SRel ctx σ prog act e e') (hnf : SigNF ctx o σ.isAux e') :
    ∀ k ∈ nestSynOccs ctx (ctx.hiAt prog.length) e,
      ∃ a, σ.contAux prog k = some a ∧ ContKeyOk ctx σ.isAux prog act k.cname k.lvls k.ds := by
  intro k hk
  rw [nestSynOccs, List.mem_eraseDups] at hk
  rcases nestSynGo_keys hσ hae e e' {} hrel hnf k hk with hk | h
  · simp at hk
  · exact h

theorem nestOcc_inst_fvar0 {names : List Name} {d : Nat} (ty : Expr) :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar d ty) k).nestOcc names 0 0 = e.nestOcc names 0 0 := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [Expr.instantiate1]
    split
    · simp [Expr.nestOcc]
    · split <;> simp [Expr.nestOcc]
  | fvar i t _ => intro k; rfl
  | sort u => intro k; rfl
  | const n us => intro k; rfl
  | lit l => intro k; rfl
  | app f a ihf iha => intro k; simp [Expr.instantiate1, Expr.nestOcc, ihf, iha]
  | lam t b mm iht ihb => intro k; simp [Expr.instantiate1, Expr.nestOcc, iht, ihb]
  | forallE t b mm iht ihb => intro k; simp [Expr.instantiate1, Expr.nestOcc, iht, ihb]
  | letE t v b iht ihv ihb => intro k; simp [Expr.instantiate1, Expr.nestOcc, iht, ihv, ihb]
  | proj s i e ih => intro k; simp [Expr.instantiate1, Expr.nestOcc, ih]

/-- Instantiating at a variable keeps the spine: a head that is no
application stays none. -/
theorem inst_fvar_spine {d : Nat} {ty : Expr} (e : Expr) (k : Nat) :
    (e.instantiate1 (.fvar d ty) k).getAppFn = e.getAppFn.instantiate1 (.fvar d ty) k ∧
    (e.instantiate1 (.fvar d ty) k).getAppArgs = e.getAppArgs.map (·.instantiate1 (.fvar d ty) k) := by
  have hnapp : ∀ (h : Expr), (∀ f a, h ≠ .app f a) →
      (∀ f a, h.instantiate1 (.fvar d ty) k ≠ .app f a) := by
    intro h hh f a
    cases h with
    | app f₀ a₀ => exact absurd rfl (hh f₀ a₀)
    | bvar i =>
      simp only [Expr.instantiate1]
      split
      · simp
      · split <;> simp
    | _ => simp [Expr.instantiate1]
  have hfn : ∀ (e : Expr), ∀ f a, e.getAppFn ≠ .app f a := by
    intro e
    induction e with
    | app f a ihf _ => simpa [Expr.getAppFn] using ihf
    | _ => simp [Expr.getAppFn]
  have hsp : ∀ (h : Expr) (args : List Expr), (∀ f a, h ≠ .app f a) →
      (Expr.mkAppN h args).getAppFn = h ∧ (Expr.mkAppN h args).getAppArgs = args := by
    intro h args hh
    rw [Expr.getAppFn_mkAppN, Expr.getAppArgs_mkAppN]
    cases h with
    | app f a => exact absurd rfl (hh f a)
    | _ => simp [Expr.getAppFn, Expr.getAppArgs]
  obtain ⟨h, args, hh, rfl⟩ : ∃ h args, (∀ f a, h ≠ .app f a) ∧ e = Expr.mkAppN h args :=
    ⟨e.getAppFn, e.getAppArgs, hfn e, (Expr.mkAppN_getApp e).symm⟩
  rw [Expr.mkAppN_instantiate1]
  have h1 := hsp _ (args.map (·.instantiate1 (.fvar d ty) k)) (hnapp h hh)
  have h2 := hsp h args hh
  rw [h1.1, h1.2, h2.1, h2.2]
  exact ⟨rfl, rfl⟩

theorem NestedSig.of_inst_fvar {d : Nat} {ty e : Expr} {k : Nat}
    (h : NestedSig ctx o (e.instantiate1 (.fvar d ty) k)) : NestedSig ctx o e := by
  obtain ⟨C, us, caps, cv, hfn, hnm, hq, hf, hle, hany⟩ := h
  obtain ⟨hs1, hs2⟩ := inst_fvar_spine (d := d) (ty := ty) e k
  rw [hs1] at hfn
  have hfn' : e.getAppFn = .const C us := by
    revert hfn
    generalize e.getAppFn = h
    intro hfn
    cases h with
    | const n us' => simpa [Expr.instantiate1] using hfn
    | bvar i =>
      simp only [Expr.instantiate1] at hfn
      split at hfn
      · simp at hfn
      · split at hfn <;> simp at hfn
    | _ => simp [Expr.instantiate1] at hfn
  rw [hs2] at hle hany
  refine ⟨C, us, caps, cv, hfn', hnm, hq, hf, by simpa using hle, ?_⟩
  rw [← List.map_take, List.any_map] at hany
  obtain ⟨x, hx, hxo⟩ := List.any_eq_true.mp hany
  refine List.any_eq_true.mpr ⟨x, hx, ?_⟩
  simp only [Function.comp, Official.PosOracle.occ] at hxo ⊢
  rw [nestOcc_inst_fvar0] at hxo
  exact hxo

/-- Official's normal form survives opening a binder at a variable. -/
theorem SigNF.inst_fvar {isAux : Name → Bool} {d : Nat} {ty : Expr} :
    ∀ {e : Expr}, SigNF ctx o isAux e → ∀ k, SigNF ctx o isAux (e.instantiate1 (.fvar d ty) k) := by
  intro e h
  induction h with
  | aux ha =>
    intro k
    rw [Expr.mkAppN_instantiate1]
    exact .aux ha
  | mem hn _ ih =>
    intro k
    rw [Expr.mkAppN_instantiate1]
    refine .mem hn fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact ih x hx k
  | app hns _ _ ihf iha =>
    intro k
    exact .app (fun h => hns (NestedSig.of_inst_fvar (e := .app _ _) h)) (ihf k) (iha k)
  | lam _ _ iht ihb => intro k; exact .lam (iht k) (ihb (k + 1))
  | forallE _ _ iht ihb => intro k; exact .forallE (iht k) (ihb (k + 1))
  | letE _ _ _ iht ihv ihb => intro k; exact .letE (iht k) (ihv k) (ihb (k + 1))
  | proj _ ih => intro k; exact .proj (ih k)
  | bvar i =>
    intro k
    simp only [Expr.instantiate1]
    split
    · exact .fvar _ _
    · split
      · exact .bvar _
      · exact .bvar _
  | fvar i t => intro k; exact .fvar i t
  | sort u => intro k; exact .sort u
  | lit l => intro k; exact .lit l
  | const n us => intro k; exact .const n us

end Syn

/-! ## The run never rejects -/

section Run

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {σ : SigmaCtx}
  {o : Official.PosOracle}

/-- **(A) at a field, at one fuel**: official's `check_positivity`
accepting a related σ-term makes the walk's field run succeed or decline. -/
@[expose] def FieldNR (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (σ : SigmaCtx)
    (o : Official.PosOracle) (f : Nat) (prog : List NestHole) (act : List NestKey) : Prop :=
  ∀ fuelO dep kb e e' st, ctx.hiAt prog.length ≤ dep → SRel ctx σ prog act e e' →
    Official.checkPositivity o fuelO dep e' = .ok () → RInv ctx st act →
    OkOr (fun r => RInv ctx r.2.2 act) (nestPos ops env ctx f prog dep kb e st)

/-- **(A) at a field's syntactic pass, at one fuel.** -/
@[expose] def SynNR (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (σ : SigmaCtx)
    (o : Official.PosOracle) (f : Nat) (prog : List NestHole) (act : List NestKey) : Prop :=
  ∀ skip e e' st, SRel ctx σ prog act e e' → SigNF ctx o σ.isAux e' → RInv ctx st act →
    OkOr (fun st' => RInv ctx st' act) (nestSyn ops env ctx f prog skip e st)

/-- **(A) at a telescope**: official's field loop accepting a related
σ-constructor makes the walk's field loop succeed or decline. -/
theorem nestFields_nr {f : Nat} {prog : List NestHole} {act : List NestKey}
    (hF : FieldNR ops env ctx σ o f prog act) (hS : SynNR ops env ctx σ o f prog act)
    (hσ : SigmaOk ctx σ o) {self : Name} {fuelO base : Nat} {err : CheckError}
    (hbase : ctx.hiAt prog.length ≤ base) :
    ∀ (nF j : Nat) (cur ct' : Expr) (nb : Nat) (st : NestState), SRel ctx σ prog act cur ct' →
      SigNF ctx o σ.isAux ct' → nF ≤ cur.piArity →
      Official.checkCtorPos o self fuelO nb (base + j) ct' = .ok () → RInv ctx st act →
      OkOr (fun r => RInv ctx r.2.2.2 act)
        (nestFields (nestPos ops env ctx f) (nestSyn ops env ctx f) prog base err nF j cur st) := by
  intro nF
  induction nF with
  | zero =>
    intro j cur ct' nb st _ _ _ _ hI
    exact hI
  | succ nF ih =>
    intro j cur ct' nb st hrel hnf hpi hchk hI
    cases cur with
    | forallE a b bm =>
      obtain ⟨a', b', rfl, hra, hrb⟩ := hrel.forallE_inv_left
      obtain ⟨hna, hnb⟩ := hnf.forallE_inv
      cases nb with
      | zero => simp [Official.checkCtorPos, throw, throwThe, MonadExceptOf.throw] at hchk
      | succ nb =>
        simp only [Official.checkCtorPos, bind, Except.bind] at hchk
        split at hchk
        · simp at hchk
        rename_i u hpos
        rw [nestFields]
        refine OkOr.bind (hF fuelO (base + j) 0 a a' st (by omega) hra hpos hI) ?_
        rintro ⟨k, nd, st₁⟩ hI₁
        refine OkOr.bind (hS _ a a' st₁ hra hna hI₁) ?_
        intro st₂ hI₂
        have hrb' := SRel.instantiate1 hσ (.fvar (i := base + j) (Or.inr (by omega)) hra) hrb 0
        have hpi' : nF ≤ (b.instantiate1 (.fvar (base + j) a)).piArity := by
          rw [piArity_instantiate1]; simp only [Expr.piArity] at hpi; omega
        refine OkOr.bind (ih (j + 1) _ _ nb st₂ hrb' (hnb.inst_fvar 0) hpi'
          (by rw [show base + (j + 1) = base + j + 1 by omega]; exact hchk) hI₂) ?_
        · rintro ⟨ks, nds, res, st₃⟩ hI₃
          exact hI₃
    | _ => simp [Expr.piArity] at hpi

/-- **The telescope's end**: official's field loop accepting a related
σ-constructor, the walk's field loop's result (`nF` fields opened) is
related to a σ-residual official's loop also accepts. -/
theorem nestFields_end (hσ : SigmaOk ctx σ o) {prog : List NestHole} {act : List NestKey}
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    {syn : List NestHole → List NestKey → Expr → NestState → CheckM NestState}
    {self : Name} {fuelO base : Nat} {err : CheckError} (hbase : ctx.hiAt prog.length ≤ base) :
    ∀ (nF j : Nat) (cur ct' : Expr) (nb : Nat) (st : NestState) ks nds res st',
      SRel ctx σ prog act cur ct' →
      Official.checkCtorPos o self fuelO nb (base + j) ct' = .ok () →
      nestFields rec syn prog base err nF j cur st = .ok (ks, nds, res, st') →
      ∃ ct'' nb', SRel ctx σ prog act res ct'' ∧
        Official.checkCtorPos o self fuelO nb' (base + j + nF) ct'' = .ok () ∧
        res.piArity + nF = cur.piArity := by
  intro nF
  induction nF with
  | zero =>
    intro j cur ct' nb st ks nds res st' hrel hchk h
    simp only [nestFields, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl, -⟩ := h
    exact ⟨ct', nb, hrel, by simpa using hchk, by simp⟩
  | succ nF ih =>
    intro j cur ct' nb st ks nds res st' hrel hchk h
    cases cur with
    | forallE a b bm =>
      obtain ⟨a', b', rfl, hra, hrb⟩ := hrel.forallE_inv_left
      cases nb with
      | zero => simp [Official.checkCtorPos, throw, throwThe, MonadExceptOf.throw] at hchk
      | succ nb =>
        simp only [Official.checkCtorPos, bind, Except.bind] at hchk
        split at hchk
        · simp at hchk
        simp only [nestFields, bind, Except.bind] at h
        split at h
        · simp at h
        split at h
        · simp at h
        split at h
        · simp at h
        rename_i r₃ h₃
        simp only [pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨ks₃, nds₃, res₃, st₃⟩ := r₃
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, -, rfl, rfl⟩ := h
        have hrb' := SRel.instantiate1 hσ (.fvar (i := base + j) (Or.inr (by omega)) hra) hrb 0
        obtain ⟨ct'', nb', hr, hc, har⟩ := ih (j + 1) _ _ nb _ ks₃ nds₃ res₃ st₃ hrb'
          (by rw [show base + (j + 1) = base + j + 1 by omega]; exact hchk) h₃
        refine ⟨ct'', nb', hr, by rw [show base + j + (nF + 1) = base + (j + 1) + nF by omega]; exact hc,
          ?_⟩
        rw [piArity_instantiate1] at har
        simp only [Expr.piArity]; omega
    | _ => simp [nestFields, throw, throwThe, MonadExceptOf.throw] at h

/-- Official's constructor loop at a non-`Π` residual is the result check. -/
theorem validAt_of_checkCtorPos {self : Name} {fuelO nb dep : Nat} {t : Expr}
    (hnp : ∀ a b bm, t ≠ .forallE a b bm)
    (h : Official.checkCtorPos o self fuelO nb dep t = .ok ()) : o.validAt self t = true := by
  cases nb with
  | zero => simp [Official.checkCtorPos, throw, throwThe, MonadExceptOf.throw] at h
  | succ nb =>
    cases t with
    | forallE a b bm => exact absurd rfl (hnp a b bm)
    | _ =>
      simp only [Official.checkCtorPos] at h
      split at h
      · assumption
      · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A walk occurrence-free index from official's occurrence-free index. -/
theorem noOcc_of_srel (hσ : SigmaOk ctx σ o) {prog : List NestHole} {act : List NestKey}
    {x x' : Expr} (h : SRel ctx σ prog act x x') (h' : (!o.occ x') = true) :
    (!x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length)) = true := by
  cases hx : x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length)
  · rfl
  · rw [h.occ_of hσ hx] at h'; exact absurd h' (by decide)

/-- **The result check at a member constructor, from official's**: a
walk telescope end related to a σ-residual official's result check
accepts at a member is its member's hole applied, its indices free of
the block. -/
theorem memberResult_of (hσ : SigmaOk ctx σ o) {self : Name} {res ct'' : Expr}
    (hrel : SRel ctx σ [] [] res ct'') (hself : ctx.names.contains self = true)
    (hv : o.validAt self ct'' = true) :
    (nestResHead res && (res.getAppArgs.drop ctx.nP).all
      (fun a => !a.nestOcc ctx.names ctx.nP (ctx.hiAt 0))) = true := by
  simp only [Official.PosOracle.validAt, Bool.and_eq_true, beq_iff_eq] at hv
  obtain ⟨⟨⟨hfn, -⟩, -⟩, hidx⟩ := hv
  obtain ⟨t, ty, -, hfn', -, -, hargs⟩ := (hrel.spine hσ hfn).1 hself
  have hps : o.ps.length = ctx.nP := by rw [hσ.ps, hσ.psEq, hσ.psLen]
  rw [hps] at hidx
  simp only [nestResHead, hfn', Bool.true_and, List.all_eq_true]
  intro a ha
  exact Rel2.forall_left (P := fun a => (!a.nestOcc ctx.names ctx.nP (ctx.hiAt 0)) = true)
    (Q := fun b => (!o.occ b) = true) (fun a b hab hb => noOcc_of_srel hσ hab hb)
    (Rel2.drop ctx.nP hargs) (fun b hb => List.all_eq_true.mp hidx b hb) a ha

/-- **THE NAMED HYPOTHESIS `InferSim`: `inferType` does not observe the
σ-replacement** — the typing counterpart of `WhnfSim`, restricted to the
terms official typed (sanctioned; not proved: official's type checker is
not transcribed, `Official.TypingOracle`).  (ctor) official's
`check_constructors` `tc().check` accepting a σ-constructor type
(`T.ctorOk`, `inductive.cpp` v4.34.0 :469) makes the walk's `inferType`
of every related walk term succeed or decline, and `ensureSort` of the
inferred type succeed or decline; (inst) official's final
`tc.check(nested)` (:1320–1323) accepting a nested application's
read-back `I Ds` makes the walk's `inferType` of the instantiation
`I ds` (its holes typed by their containers' formers) succeed or
decline. -/
@[expose] def InferSim (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (σ : SigmaCtx)
    (T : Official.TypingOracle) : Prop :=
  (∀ (prog : List NestHole) (act : List NestKey) (dep : Nat) (e e' : Expr),
    ctx.hiAt prog.length ≤ dep → SRel ctx σ prog act e e' → T.ctorOk dep e' →
    OkOr (fun ty => OkOr (fun _ => True) (ops.ensureSort env dep ty)) (ops.inferType env dep e)) ∧
  (∀ (prog : List NestHole) (C : Name) (us : List Level) (ds : List Expr),
    T.nestedOk (rbKey ctx prog ⟨C, us, ds⟩) →
    OkOr (fun _ => True) (ops.inferType env (ctx.hiAt prog.length) (Expr.mkAppN (.const C us) ds)))

/-- **THE NAMED HYPOTHESIS U4, as a typing fact** (not proved; measured —
lane RESTRICT-FIX: official rejects every instance).  At a constructor
type official typed (`T.ctorOk`, `check_constructors` :469) related to a
walk telescope, no later field and not the result of the walked
telescope reads a field that is not ordinary (`structUsedLater`): a
value of a declared type is used in a type only through a function
mentioning the declared types, which official's typing (with the
declaration's types opaque and constructor-less) or positivity rejects. -/
@[expose] def U4Typed (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (σ : SigmaCtx)
    (T : Official.TypingOracle) : Prop :=
  ∀ (prog : List NestHole) (act : List NestKey) (crest ct' : Expr), SRel ctx σ prog act crest ct' →
    T.ctorOk (ctx.hiAt prog.length) ct' →
    ∀ nF f err st ks nds cur st',
      nestFields (nestPos ops env ctx f) (nestSyn ops env ctx f) prog (ctx.hiAt prog.length) err nF
        0 crest st = .ok (ks, nds, cur, st') →
      ((List.range nF).any fun i => ks.getD i .ordinary != .ordinary &&
        structUsedLater (closeTelescope nds (ctx.hiAt prog.length) cur) 0 i) = false

/-- **A frame constructor's obligations** (what official's acceptance must
supply at one constructor of a frame's group; discharged by the
frame-constructor relation and the side checks): its level parameters
distinct, its instantiation related to official's auxiliary constructor
(which official's field loop accepts), its typing declining at worst,
and the walked telescope's U4 and result checks. -/
@[expose] def CtorStep (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (σ : SigmaCtx)
    (o : Official.PosOracle) (prog : List NestHole) (act : List NestKey) (us : List Level)
    (ds : List Expr) (sub : Name → List Level → Option Expr) (cv : ConstantVal) (nF : Nat) :
    Prop :=
  Name.nodup cv.levelParams = true ∧
  ∃ crest ct' self fuelO nb,
    instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts sub)
      = some crest ∧
    SRel ctx σ prog act crest ct' ∧ SigNF ctx o σ.isAux ct' ∧ nF ≤ crest.piArity ∧
    Official.checkCtorPos o self fuelO nb (ctx.hiAt prog.length) ct' = .ok () ∧
    OkOr (fun ty => OkOr (fun _ => True) (ops.ensureSort env (ctx.hiAt prog.length) ty))
      (ops.inferType env (ctx.hiAt prog.length) crest) ∧
    ∀ f err st ks nds cur st',
      nestFields (nestPos ops env ctx f) (nestSyn ops env ctx f) prog (ctx.hiAt prog.length) err nF
        0 crest st = .ok (ks, nds, cur, st') →
      ((List.range nF).any fun i => ks.getD i .ordinary != .ordinary &&
        structUsedLater (closeTelescope nds (ctx.hiAt prog.length) cur) 0 i) = false ∧
      (nestResHead cur && (cur.getAppArgs.drop ds.length).all
        (fun x => !x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length))) = true

/-- **(A) at a frame's constructors.** -/
theorem nestCtors_nr {f : Nat} {prog : List NestHole} {act : List NestKey} {us : List Level}
    {ds : List Expr} {sub : Name → List Level → Option Expr}
    (hF : FieldNR ops env ctx σ o f prog act) (hS : SynNR ops env ctx σ o f prog act)
    (hσ : SigmaOk ctx σ o) :
    ∀ (cs : List (ConstantVal × Nat)) (st : NestState),
      (∀ c ∈ cs, CtorStep ops env ctx σ o prog act us ds sub c.1 c.2) → RInv ctx st act →
      OkOr (fun st' => RInv ctx st' act)
        (nestCtors ctx ops env (nestPos ops env ctx f) (nestSyn ops env ctx f) prog
          (ctx.hiAt prog.length) us ds ds.length sub cs st) := by
  intro cs
  induction cs with
  | nil => intro st _ hI; exact hI
  | cons c cs ih =>
    intro st hcs hI
    obtain ⟨cv, nF⟩ := c
    obtain ⟨hnd, crest, ct', self, fuelO, nb, hcr, hrel, hnf, hpi, hchk, htyp, hside⟩ :=
      hcs (cv, nF) List.mem_cons_self
    rw [nestCtors]
    simp only [hnd, hcr, unwrapOr, if_true, pure_bind]
    refine OkOr.bind htyp fun ty hty => OkOr.bind hty fun _ _ => ?_
    have hfl := nestFields_nr (err := .invalid "nested positivity: invalid nested inductive \
      datatype, its constructor type does not bind its fields (official: ill-formed constructor)")
      hF hS hσ (self := self) (fuelO := fuelO) (base := ctx.hiAt prog.length) (Nat.le_refl _)
      nF 0 crest ct' nb st hrel hnf hpi (by simpa using hchk) hI
    revert hfl
    cases hres : nestFields (nestPos ops env ctx f) (nestSyn ops env ctx f) prog
      (ctx.hiAt prog.length) (.invalid "nested positivity: invalid nested inductive datatype, \
      its constructor type does not bind its fields (official: ill-formed constructor)") nF 0
      crest st with
    | error e => intro h; exact h
    | ok r =>
      intro hI₁
      obtain ⟨ks, nds, cur, st₁⟩ := r
      obtain ⟨hu4, hrs⟩ := hside f _ st ks nds cur st₁ hres
      simp only [bind, Except.bind]
      rw [if_neg (by rw [hu4]; simp)]
      simp only [hrs]
      exact ih st₁ (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) hI₁

/-- **A frame's obligations** at a fresh instantiation `C.{us} ds` walked
under the stack `wp` with the in-progress list `act`: its former's and
its group-mates' checks decline at worst; for the group they build, the
instantiation's typing declines at worst (K.52), the invariant `I` holds
under the frame, and every constructor of the group meets `CtorStep`. -/
@[expose] def FrameStep (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (σ : SigmaCtx)
    (o : Official.PosOracle) (I : List NestHole → List NestKey → Prop) (act : List NestKey)
    (wp : List NestHole) (C : Name) (us : List Level) (ds : List Expr) : Prop :=
  (∀ m ∈ C :: nestFrameMates ctx C,
    OkOr (fun _ => True) (nestInstType (m := CheckM) ctx (ctx.hiAt wp.length) ⟨m, us, ds⟩)) ∧
  ∀ grp : List (Name × Expr), grp ≠ [] → (grp.headD default).1 = C →
    grp.map (·.1) = C :: nestFrameMates ctx C →
    (∀ p ∈ grp, ∃ nI, nestInstType (m := CheckM) ctx (ctx.hiAt wp.length) ⟨p.1, us, ds⟩
      = .ok (nI, p.2)) →
    OkOr (fun _ => True)
      (ops.inferType env (ctx.hiAt wp.length) (Expr.mkAppN (.const C us) ds)) ∧
    I ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp) (grpKeys us ds grp ++ act) ∧
    ∃ ctors, groupCtors ctx ds.length (grp.map (·.1)) = some ctors ∧
      ∀ c ∈ ctors, CtorStep ops env ctx σ o ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp)
        (grpKeys us ds grp ++ act) us ds (grpSub us (ctx.hiAt wp.length) grp) c.1 c.2

theorem nestGrowGroup_okor {hi : Nat} {us : List Level} {ds : List Expr} :
    ∀ (names : List Name) (grp : List (Name × Expr)),
      (∀ m ∈ names, OkOr (fun _ => True) (nestInstType (m := CheckM) ctx hi ⟨m, us, ds⟩)) →
      OkOr (fun grp' => ∃ ext, grp' = grp ++ ext ∧ ext.map (·.1) = names ∧
          ∀ p ∈ ext, ∃ nI, nestInstType (m := CheckM) ctx hi ⟨p.1, us, ds⟩ = .ok (nI, p.2))
        (nestGrowGroup (m := CheckM) ctx hi us ds names grp)
  | [], grp, _ => ⟨[], by simp, rfl, by simp⟩
  | m :: names, grp, h => by
    rw [nestGrowGroup]
    refine OkOr.bind_eq (h m List.mem_cons_self) fun r hr _ => ?_
    obtain ⟨nI, cty⟩ := r
    refine OkOr.mono (nestGrowGroup_okor names _ (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')))
      ?_
    rintro grp' ⟨ext, rfl, hmap, hext⟩
    refine ⟨(m, cty) :: ext, by simp, by simp [hmap], ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨nI, hr⟩
    · exact hext p hp

/-- **(A) at a frame**: its obligations and the walk's field and
syntactic runs under it (one fuel lower) make the frame's run succeed or
decline. -/
theorem nestFrame_nr {f : Nat} {I : List NestHole → List NestKey → Prop} {act : List NestKey}
    {wp : List NestHole} {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
    {st : NestState}
    (hIH : ∀ prog act, I prog act → FieldNR ops env ctx σ o f prog act ∧ SynNR ops env ctx σ o f prog act)
    (hσ : SigmaOk ctx σ o)
    (hfs : OkOr (fun _ => True)
        (ops.inferType env (ctx.hiAt wp.length) (Expr.mkAppN (.const (grp.headD default).1 us) ds)) ∧
      I ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp) (grpKeys us ds grp ++ act) ∧
      ∃ ctors, groupCtors ctx ds.length (grp.map (·.1)) = some ctors ∧
        ∀ c ∈ ctors, CtorStep ops env ctx σ o ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp)
          (grpKeys us ds grp ++ act) us ds (grpSub us (ctx.hiAt wp.length) grp) c.1 c.2)
    (hI : RInv ctx st (grpKeys us ds grp ++ act)) :
    OkOr (fun st' => RInv ctx st' (grpKeys us ds grp ++ act))
      (nestFrame ctx ops env (nestPos ops env ctx f) (nestSyn ops env ctx f) wp
        (ctx.hiAt wp.length) us ds ds.length grp st) := by
  obtain ⟨hty, hI', ctors, hctors, hcs⟩ := hfs
  obtain ⟨hF, hS⟩ := hIH _ _ hI'
  rw [nestFrame]
  refine OkOr.bind hty fun _ _ => ?_
  obtain ⟨st₁, h₁, hI₁⟩ := nestGroupCtors_ok (ctx := ctx) (nPc := ds.length) _ st ctors hctors hI
  simp only [bind, Except.bind, h₁]
  have hlen : ctx.hiAt wp.length + grp.length =
      ctx.hiAt ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp).length := by
    simp [NestCtx.hiAt, grpNews]; omega
  have := nestCtors_nr (us := us) (ds := ds) (sub := grpSub us (ctx.hiAt wp.length) grp) hF hS hσ
    ctors st₁ hcs hI₁
  rw [← hlen] at this
  rw [grpNews_mapIdx]
  exact this

/-- **(A) at a new frame** (`nestContNew`). -/
theorem nestContNew_nr {f : Nat} {I : List NestHole → List NestKey → Prop} {prog : List NestHole}
    {kb : Nat} {c : Name} {us : List Level} {ds : List Expr} {nPc : Nat} {old : Option Nat}
    {st : NestState} {act : List NestKey}
    (hIH : ∀ prog act, I prog act → FieldNR ops env ctx σ o f prog act ∧ SynNR ops env ctx σ o f prog act)
    (hσ : SigmaOk ctx σ o) (hI : RInv ctx st act) (hnPc : ds.length = nPc)
    (hfs : FrameStep ops env ctx σ o I act (nestWalkStack ctx prog ds) c us ds) :
    OkOr (fun r => RInv ctx r.2 act)
      (nestContNew ctx ops env (nestPos ops env ctx f) (nestSyn ops env ctx f) prog kb c us ds nPc
        old st) := by
  subst hnPc
  obtain ⟨hinst, hgrp⟩ := hfs
  rw [nestContNew]
  refine OkOr.bind_eq (hinst c List.mem_cons_self) fun ni hni _ => ?_
  refine OkOr.bind (nestGrowGroup_okor _ [(c, ni.2)]
    (fun m hm => hinst m (List.mem_cons_of_mem _ hm))) ?_
  rintro grp ⟨ext, rfl, hmap, hext⟩
  have hall : ∀ p ∈ [(c, ni.2)] ++ ext, ∃ nI, nestInstType (m := CheckM) ctx
      (ctx.hiAt (nestWalkStack ctx prog ds).length) ⟨p.1, us, ds⟩ = .ok (nI, p.2) := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨ni.1, hni⟩
    · exact hext p hp
  have hg := hgrp ([(c, ni.2)] ++ ext) (by simp) rfl (by simp [hmap]) hall
  simp only [List.singleton_append] at hg ⊢
  have hfr := nestFrame_nr (f := f) (I := I) (act := act) (wp := nestWalkStack ctx prog ds)
    (us := us) (ds := ds) (grp := (c, ni.2) :: ext)
    (st := { st with active := grpKeys us ds ((c, ni.2) :: ext) ++ st.active })
    hIH hσ (by simpa using hg) ⟨by rw [hI.1], hI.2⟩
  refine OkOr.bind hfr fun st₁ hI₁ => ?_
  obtain ⟨st₂, hacc, hact₂, hco₂⟩ := nestAcceptGroup_ok (ctx := ctx)
    (hi := ctx.hiAt (nestWalkStack ctx prog ds).length) (us := us) (ds := ds) ext
    { st₁ with active := st.active }
    (fun p hp => by
      obtain ⟨nI', h'⟩ := hext p hp
      exact ⟨nI', p.2, h'⟩)
  simp only [List.drop_succ_cons, List.drop_zero, hacc, bind, Except.bind]
  have hI₂ : RInv ctx st₂ act := ⟨by rw [hact₂]; exact hI.1, by rw [hco₂]; exact hI₁.2⟩
  cases old with
  | some q => exact ⟨hI₂.1, hI₂.2⟩
  | none => exact ⟨hI₂.1, hI₂.2⟩

/-- **(A) at a fresh instantiation met** (`nestContKey`). -/
theorem nestContKey_nr {f : Nat} {I : List NestHole → List NestKey → Prop} {prog : List NestHole}
    {kb : Nat} {c : Name} {us : List Level} {ds : List Expr} {nPc : Nat} {st : NestState}
    {act : List NestKey}
    (hIH : ∀ prog act, I prog act → FieldNR ops env ctx σ o f prog act ∧ SynNR ops env ctx σ o f prog act)
    (hσ : SigmaOk ctx σ o) (hI : RInv ctx st act) (hnPc : ds.length = nPc)
    (hfresh : ∀ h ∈ prog, h.key ≠ ⟨c, us, ds⟩) (hact : (⟨c, us, ds⟩ : NestKey) ∉ act)
    (hfs : FrameStep ops env ctx σ o I act (nestWalkStack ctx prog ds) c us ds) :
    OkOr (fun r => RInv ctx r.2 act)
      (nestContKey ctx ops env (nestPos ops env ctx f) (nestSyn ops env ctx f) prog kb c us ds nPc
        st) := by
  unfold nestContKey
  have hprog : prog.any (·.key == (⟨c, us, ds⟩ : NestKey)) = false := by
    rw [List.any_eq_false]
    intro h hh
    simpa using hfresh h hh
  have hactc : st.active.contains ⟨c, us, ds⟩ = false := by
    rw [hI.1]; simpa using hact
  rw [if_neg (by rw [hprog, hactc]; simp)]
  split
  · split
    · exact ⟨hI.1, hI.2⟩
    · exact nestContNew_nr hIH hσ hI hnPc hfs
  · exact nestContNew_nr hIH hσ hI hnPc hfs

/-- **(A) at the container case** (`nestCont`). -/
theorem nestCont_nr {f : Nat} {I : List NestHole → List NestKey → Prop} {prog : List NestHole}
    {kb : Nat} {c : Name} {us : List Level} {args : List Expr} {st : NestState}
    {act : List NestKey} {L : List (ConstantVal × Nat)} {nPc nI : Nat}
    (hIH : ∀ prog act, I prog act → FieldNR ops env ctx σ o f prog act ∧ SynNR ops env ctx σ o f prog act)
    (hσ : SigmaOk ctx σ o) (hI : RInv ctx st act) (hC : nestContainer ctx c = some (nPc, L))
    (hlen : args.length = nPc + nI) (hquot : c ≠ quotName)
    (hidx : ∀ x ∈ args.drop nPc, x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)
    (hds : ∀ x ∈ args.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length)
    (hinst : OkOr (fun r => r.1 = nI)
      (nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨c, us, args.take nPc⟩))
    (hfresh : ∀ h ∈ prog, h.key ≠ ⟨c, us, args.take nPc⟩)
    (hact : (⟨c, us, args.take nPc⟩ : NestKey) ∉ act)
    (hfs : FrameStep ops env ctx σ o I act (nestWalkStack ctx prog (args.take nPc)) c us
      (args.take nPc)) :
    OkOr (fun r => RInv ctx r.2 act)
      (nestCont ctx ops env (nestPos ops env ctx f) (nestSyn ops env ctx f) prog kb c us args st) := by
  unfold nestCont
  simp only [hI.lookup c, hC, unwrapOr, pure_bind]
  rw [if_neg (by
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.all_eq_false,
      not_or, not_exists, not_and, Bool.not_eq_eq_eq_not, Bool.not_true]
    exact ⟨by omega, fun x hx => by simpa using hidx x hx⟩)]
  rw [if_neg (by simpa using hquot)]
  rw [if_pos (by
    rw [List.all_eq_true]
    intro x hx
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact hds x hx)]
  refine OkOr.bind hinst fun ni hni => ?_
  rw [if_pos (by simp [hlen, hni])]
  have hI' := hI.insert c
  exact nestContKey_nr hIH hσ hI' (by simp; omega) hfresh hact hfs

/-- **(A) at one syntactic occurrence** (`nestSynKey`). -/
theorem nestSynKey_nr {f : Nat} {I : List NestHole → List NestKey → Prop} {prog : List NestHole}
    {skip : List NestKey} {key : NestKey} {st : NestState} {act : List NestKey}
    {L : List (ConstantVal × Nat)}
    (hIH : ∀ prog act, I prog act → FieldNR ops env ctx σ o f prog act ∧ SynNR ops env ctx σ o f prog act)
    (hσ : SigmaOk ctx σ o) (hI : RInv ctx st act)
    (hds : ∀ x ∈ key.ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length)
    (hnm : ctx.names.contains key.cname = false) (hquot : key.cname ≠ quotName)
    (hC : nestContainer ctx key.cname = some (key.ds.length, L))
    (hfs : FrameStep ops env ctx σ o I act (nestWalkStack ctx prog key.ds) key.cname key.lvls
      key.ds) :
    OkOr (fun st' => RInv ctx st' act)
      (nestSynKey ctx ops env (nestPos ops env ctx f) (nestSyn ops env ctx f) prog skip key st) := by
  unfold nestSynKey
  rw [if_neg (by
    simp only [Bool.not_eq_true', Bool.not_eq_false]
    rw [List.all_eq_true]
    intro x hx
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact hds x hx)]
  split
  · exact hI
  rw [if_neg (by rw [hnm, Bool.false_or]; simpa using hquot)]
  have hI₀ := hI.insert key.cname
  rw [hI.lookup key.cname, hC]
  simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
  split
  · split
    · exact ⟨hI₀.1, hI₀.2⟩
    · exact OkOr.bind (nestContNew_nr (kb := 0) hIH hσ hI₀ rfl hfs) fun r hr => hr
  · exact OkOr.bind (nestContNew_nr (kb := 0) hIH hσ hI₀ rfl hfs) fun r hr => hr

/-- **(A) at a field's syntactic occurrences** (`nestSynKeys`). -/
theorem nestSynKeys_nr {f : Nat} {I : List NestHole → List NestKey → Prop} {prog : List NestHole}
    {skip : List NestKey} {act : List NestKey}
    (hIH : ∀ prog act, I prog act → FieldNR ops env ctx σ o f prog act ∧ SynNR ops env ctx σ o f prog act)
    (hσ : SigmaOk ctx σ o) :
    ∀ (keys : List NestKey) (st : NestState), RInv ctx st act →
      (∀ k ∈ keys, (∀ x ∈ k.ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length) ∧
        ctx.names.contains k.cname = false ∧ k.cname ≠ quotName ∧
        (∃ L, nestContainer ctx k.cname = some (k.ds.length, L)) ∧
        FrameStep ops env ctx σ o I act (nestWalkStack ctx prog k.ds) k.cname k.lvls k.ds) →
      OkOr (fun st' => RInv ctx st' act)
        (nestSynKeys ctx ops env (nestPos ops env ctx f) (nestSyn ops env ctx f) prog skip keys st)
  | [], st, hI, _ => hI
  | k :: ks, st, hI, hks => by
    rw [nestSynKeys]
    obtain ⟨hds, hnm, hq, ⟨L, hC⟩, hfs⟩ := hks k List.mem_cons_self
    exact OkOr.bind (nestSynKey_nr hIH hσ hI hds hnm hq hC hfs) fun st' hI' =>
      nestSynKeys_nr hIH hσ ks st' hI' (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))

/-- **The frames' obligations** under an invariant `I` of the (stack,
in-progress list) pairs the walk reaches: the frame holes' arity, and —
at every fresh instantiation official reads as an auxiliary type — its
container, its former's check at the occurrence (agreeing with official's
index count), and its frame (`FrameStep`). -/
structure Steps (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (σ : SigmaCtx)
    (o : Official.PosOracle) (I : List NestHole → List NestKey → Prop) : Prop where
  arity : ∀ prog act, I prog act → FrameArity ctx σ o prog
  key : ∀ prog act C us ds a, I prog act → σ.contAux prog ⟨C, us, ds⟩ = some a →
    ContKeyOk ctx σ.isAux prog act C us ds →
    (∃ L, nestContainer ctx C = some (ds.length, L)) ∧
    OkOr (fun r => r.1 = o.nIdx a)
      (nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨C, us, ds⟩) ∧
    FrameStep ops env ctx σ o I act (nestWalkStack ctx prog ds) C us ds

/-- **(A), RUN-LEVEL, AT EVERY FUEL.**  Under `WhnfSim` and the frames'
obligations (`Steps`), official's positivity check accepting a σ-term
makes the walk's field run on every related walk term succeed or
decline — and likewise the syntactic pass — at every fuel. -/
theorem run_nr (hσ : SigmaOk ctx σ o) (hae : AuxEnvOk ctx σ) (hsim : WhnfSim ops env ctx σ o.whnf)
    {I : List NestHole → List NestKey → Prop} (hst : Steps ops env ctx σ o I) :
    ∀ f prog act, I prog act →
      FieldNR ops env ctx σ o f prog act ∧ SynNR ops env ctx σ o f prog act := by
  intro f
  induction f with
  | zero =>
    intro prog act _
    refine ⟨fun fuelO dep kb e e' st _ _ _ _ => ?_, fun skip e e' st _ _ _ => ?_⟩
    · rw [nestPos]; exact ⟨_, rfl⟩
    · rw [nestSyn]; exact ⟨_, rfl⟩
  | succ f ih =>
    intro prog act hIpa
    refine ⟨?_, ?_⟩
    · -- the field
      intro fuelO dep kb e e' st hdep hrel hchk hI
      cases fuelO with
      | zero => simp [Official.checkPositivity, throw, throwThe, MonadExceptOf.throw] at hchk
      | succ fuelO =>
      simp only [Official.checkPositivity, bind, Except.bind] at hchk
      split at hchk
      · simp at hchk
      rename_i w' hw'
      obtain ⟨w, hw, hrw⟩ := hsim prog act dep e e' w' hdep hrel hw'
      rw [nestPos, hw]
      refine OkOr.ok_bind ?_
      try dsimp only
      by_cases hocc : o.occ w' = true
      · rw [if_neg (by simp [hocc])] at hchk
        have hwocc := hrw.of_occ hσ hocc
        rw [if_neg (by simp [hwocc])]
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
          try dsimp only
          rw [if_neg (by simp [ha])]
          exact OkOr.bind ((ih prog act hIpa).1 fuelO (dep + 1) (kb + 1) _ _ st (by omega) hrb' hchk hI)
            fun r hr => hr
        · -- a valid application of a declared type
          rename_i hnpi
          have hnpiw : ∀ a b bm, w ≠ .forallE a b bm := by
            rintro a b bm rfl
            obtain ⟨a', b', rfl, -, -⟩ := hrw.forallE_inv_left
            exact hnpi a' b' bm rfl
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
            split
            · rename_i a b bm; exact absurd rfl (hnpiw a b bm)
            try dsimp only
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
              rw [hfx]
              try dsimp only
              rw [if_pos (by simp [NestCtx.hiAt]; omega)]
              rw [if_pos (by
                simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
                  Bool.not_eq_eq_eq_not, Bool.not_true]
                refine ⟨⟨?_, hpar⟩, hfree⟩
                simpa using hlen)]
              exact hI
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
                have hF : (Expr.mkAppN (Expr.mkAppN (.fvar (ctx.hiAt 0 + i) ty) hk.key.ds) is).getAppFn
                    = .fvar (ctx.hiAt 0 + i) ty := by
                  rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN]; rfl
                rw [hF]
                try dsimp only
                rw [if_neg (by
                  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
                  intro _
                  exact Nat.not_lt.mpr (Nat.le_add_right _ _))]
                rw [if_pos (by simp [NestCtx.hiAt]; omega)]
                rw [show ctx.hiAt 0 + i - ctx.hiAt 0 = i by omega, hk']
                try dsimp only
                rw [if_pos (by rw [hA]; simp)]
                rw [if_pos (by rw [hA]; simpa using hisfree)]
                rw [if_pos (by
                  rw [hA, List.length_append, (hst.arity prog act hIpa) i hk n0 hk' hfa, hisl, hislen]
                  simp)]
                exact hI
              · obtain ⟨⟨L, hC⟩, hinst, hfs⟩ := hst.key prog act C us ds n0 hIpa hca hok
                have hA : (Expr.mkAppN (Expr.mkAppN (.const C us) ds) is).getAppArgs = ds ++ is := by
                  rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN]; simp [Expr.getAppArgs]
                have hF : (Expr.mkAppN (Expr.mkAppN (.const C us) ds) is).getAppFn = .const C us := by
                  rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN]; rfl
                have htk : (ds ++ is).take ds.length = ds := by simp
                rw [hF]
                try dsimp only
                rw [if_neg (by simpa using hok.1)]
                rw [hA]
                refine OkOr.bind (nestCont_nr (ih) hσ hI hC
                  (nI := o.nIdx n0) (by rw [List.length_append, hisl, hislen])
                  hok.2.1 (by simpa using hisfree) (by rw [htk]; exact hok.2.2.1)
                  (by rw [htk]; exact hinst) (by rw [htk]; exact hok.2.2.2.2.2.1)
                  (by rw [htk]; exact hok.2.2.2.2.2.2.1) (by rw [htk]; exact hfs)) fun r hr => ?_
                exact hr
          · rw [if_neg hv] at hchk
            simp [throw, throwThe, MonadExceptOf.throw] at hchk
      · -- no declared type: the walk's `const`
        have hwn : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false := by
          cases hc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length)
          · rfl
          · exact absurd (hrw.occ_of hσ hc) hocc
        rw [if_pos (by simp [hwn])]
        exact hI
    · -- the syntactic pass
      intro skip e e' st hrel hnf hI
      rw [nestSyn]
      refine nestSynKeys_nr ih hσ _ st hI fun k hk => ?_
      obtain ⟨a, hca, hok⟩ := nestSynOccs_keys hσ hae hrel hnf k hk
      obtain ⟨hL, -, hfs⟩ := hst.key prog act k.cname k.lvls k.ds a hIpa hca hok
      exact ⟨hok.2.2.1, hok.1, hok.2.1, hL, hfs⟩

/-- **A member constructor's M3** (`holesApplied` on the walked telescope's
normal form), at every output its field loop can produce. -/
@[expose] def MemberSide (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (nF : Nat)
    (crest : Expr) : Prop :=
  ∀ err st ks nds cur st',
    nestFields (nestPos ops env ctx (whnfWalkFuel crest)) (nestSyn ops env ctx (whnfWalkFuel crest))
      [] (ctx.hiAt 0) err nF 0 crest st = .ok (ks, nds, cur, st') →
    (closeTelescope nds (ctx.hiAt 0) cur).holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true

/-- **(A) at a member constructor.** -/
theorem nestMemberCtor_nr (hσ : SigmaOk ctx σ o) (hae : AuxEnvOk ctx σ)
    (hsim : WhnfSim ops env ctx σ o.whnf) {I : List NestHole → List NestKey → Prop}
    (hst : Steps ops env ctx σ o I) (hI0 : I [] []) {self : Name} {fuelO nb nF : Nat}
    {crest ct' : Expr} (hrel : SRel ctx σ [] [] crest ct') (hnf : SigNF ctx o σ.isAux ct')
    (hpi : crest.piArity = nF)
    (hchk : Official.checkCtorPos o self fuelO nb (ctx.hiAt 0) ct' = .ok ())
    (hself : ctx.names.contains self = true) {T : Official.TypingOracle}
    (hu4 : U4Typed ops env ctx σ T) (hty : T.ctorOk (ctx.hiAt 0) ct')
    (hside : MemberSide ops env ctx nF crest) {st : NestState} (hI : RInv ctx st []) :
    OkOr (fun r => RInv ctx r.2.2 []) (nestMemberCtor ops env ctx nF crest st) := by
  obtain ⟨hF, hS⟩ := run_nr hσ hae hsim hst (whnfWalkFuel crest) [] [] hI0
  have hfl := nestFields_nr (err := .invalid "nested positivity: a constructor type does not bind \
    its fields (official: ill-formed constructor)") hF hS hσ (self := self) (fuelO := fuelO)
    (base := ctx.hiAt 0) (by simp) nF 0 crest ct' nb st hrel hnf (by omega) (by simpa using hchk) hI
  rw [nestMemberCtor]
  revert hfl
  cases hres : nestFields (nestPos ops env ctx (whnfWalkFuel crest))
    (nestSyn ops env ctx (whnfWalkFuel crest)) [] (ctx.hiAt 0) (.invalid "nested positivity: a \
    constructor type does not bind its fields (official: ill-formed constructor)") nF 0 crest st with
  | error e => intro h; exact h
  | ok r =>
    intro hI₁
    obtain ⟨ks, nds, cur, st₁⟩ := r
    have hu4 := hu4 [] [] crest ct' hrel hty nF _ _ st ks nds cur st₁ hres
    have hha := hside _ st ks nds cur st₁ hres
    obtain ⟨ct'', nb', hr'', hc'', har⟩ := nestFields_end hσ (by simp) nF 0 crest ct' nb st ks nds cur st₁
      hrel (by simpa using hchk) hres
    have hrs := memberResult_of hσ hr'' hself (validAt_of_checkCtorPos (fun a b bm he => by
      subst he
      obtain ⟨a₀, b₀, rfl, -, -⟩ := hr''.forallE_inv
      simp only [Expr.piArity] at har; omega) hc'')
    simp only [bind, Except.bind]
    rw [if_neg (by
      intro hc
      rw [List.any_eq_true] at hc
      obtain ⟨i, hi, hc⟩ := hc
      rw [List.any_eq_false] at hu4
      have := hu4 i hi
      revert hc this
      generalize ks.getD i .ordinary = k
      cases k <;> simp)]
    simp only [hrs, hha]
    exact hI₁

/-- **(A) FOR A WHOLE NESTED BLOCK, AT THE RUN**: under `WhnfSim` and the
frames' obligations (`Steps`), if every member constructor's walk input
is related to a σ-constructor official's positivity loop accepts (with
its non-positivity checks), then `nestedBlockPositivity` succeeds or
declines — it never rejects. -/
theorem nestedBlockPositivity_nr (hσ : SigmaOk ctx σ o) (hae : AuxEnvOk ctx σ)
    (hsim : WhnfSim ops env ctx σ o.whnf) {T : Official.TypingOracle} (hu4 : U4Typed ops env ctx σ T)
    {I : List NestHole → List NestKey → Prop}
    (hst : Steps ops env ctx σ o I) (hI0 : I [] []) {holes : List Expr}
    (hh : nestHoles ctx = some holes) {ctorss : List (List (ConstantVal × Nat))}
    (hall : ∀ cs ∈ ctorss, ∀ c ∈ cs, ∃ crest ct' self fuelO nb,
      instPisWith ctx.params (nestAbstract ctx holes c.1.type) = some crest ∧
      SRel ctx σ [] [] crest ct' ∧ SigNF ctx o σ.isAux ct' ∧ crest.piArity = c.2 ∧
      Official.checkCtorPos o self fuelO nb (ctx.hiAt 0) ct' = .ok () ∧
      ctx.names.contains self = true ∧ T.ctorOk (ctx.hiAt 0) ct' ∧
      MemberSide ops env ctx c.2 crest ∧
      (nestAbstract ctx holes c.1.type).nestOcc ctx.names 0 0 = false) :
    OkOr (fun _ => True) (nestedBlockPositivity ops env ctx ctorss) := by
  have hmem : ∀ (cs : List (ConstantVal × Nat)) (st : NestState), RInv ctx st [] →
      (∀ c ∈ cs, ∃ crest ct' self fuelO nb,
        instPisWith ctx.params (nestAbstract ctx holes c.1.type) = some crest ∧
        SRel ctx σ [] [] crest ct' ∧ SigNF ctx o σ.isAux ct' ∧ crest.piArity = c.2 ∧
        Official.checkCtorPos o self fuelO nb (ctx.hiAt 0) ct' = .ok () ∧
        ctx.names.contains self = true ∧ T.ctorOk (ctx.hiAt 0) ct' ∧
        MemberSide ops env ctx c.2 crest ∧
        (nestAbstract ctx holes c.1.type).nestOcc ctx.names 0 0 = false) →
      OkOr (fun r => RInv ctx r.2.2 []) (nestMemberCtors ops env ctx holes cs st) := by
    intro cs
    induction cs with
    | nil => intro st hI _; exact hI
    | cons c cs ih =>
      intro st hI hc
      obtain ⟨crest, ct', self, fuelO, nb, hcr, hrel, hnf, hpi, hchk, hself, hty, hside, hm2⟩ :=
        hc c List.mem_cons_self
      rw [nestMemberCtors]
      simp only [hcr, unwrapOr, pure_bind]
      refine OkOr.bind (nestMemberCtor_nr hσ hae hsim hst hI0 hrel hnf hpi hchk hself hu4 hty hside hI) ?_
      rintro ⟨ks, tyN, st₁⟩ hI₁
      simp only [nestNoMemberConst, hm2, Bool.false_eq_true, if_false, pure_bind]
      refine OkOr.bind (ih st₁ hI₁ (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc'))) ?_
      rintro ⟨kss, nss, st₂⟩ hI₂
      exact hI₂
  have hblk : ∀ (css : List (List (ConstantVal × Nat))) (st : NestState), RInv ctx st [] →
      (∀ cs ∈ css, ∀ c ∈ cs, ∃ crest ct' self fuelO nb,
        instPisWith ctx.params (nestAbstract ctx holes c.1.type) = some crest ∧
        SRel ctx σ [] [] crest ct' ∧ SigNF ctx o σ.isAux ct' ∧ crest.piArity = c.2 ∧
        Official.checkCtorPos o self fuelO nb (ctx.hiAt 0) ct' = .ok () ∧
        ctx.names.contains self = true ∧ T.ctorOk (ctx.hiAt 0) ct' ∧
        MemberSide ops env ctx c.2 crest ∧
        (nestAbstract ctx holes c.1.type).nestOcc ctx.names 0 0 = false) →
      OkOr (fun _ => True) (nestBlockCtors ops env ctx holes css st) := by
    intro css
    induction css with
    | nil => intro st _ _; trivial
    | cons cs css ih =>
      intro st hI hc
      rw [nestBlockCtors]
      refine OkOr.bind (hmem cs st hI (hc cs List.mem_cons_self)) ?_
      rintro ⟨kss, nss, st₁⟩ hI₁
      refine OkOr.bind (ih st₁ hI₁ (fun cs' hcs' => hc cs' (List.mem_cons_of_mem _ hcs'))) ?_
      intro _ _
      trivial
  rw [nestedBlockPositivity]
  simp only [hh, unwrapOr, pure_bind]
  refine OkOr.bind (hblk ctorss {} ⟨rfl, fun _ _ h => by simp at h⟩ hall) ?_
  intro _ _
  trivial

end Run

end ConLeche
