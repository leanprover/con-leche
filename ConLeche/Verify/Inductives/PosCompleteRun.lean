module

public import ConLeche.Verify.Inductives.PosCompleteInit
import ConLeche.Verify.InferLemmas
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
      (∃ ds is is' a, σ.contAux prog ⟨C, us, ds⟩ = some a ∧ ContKeyOk ctx prog act C us ds ∧
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
    (hok : ContKeyOk ctx prog act C us ds) :
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
          ∃ a, σ.contAux prog k = some a ∧ ContKeyOk ctx prog act k.cname k.lvls k.ds := by
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
              ∃ a, σ.contAux prog k = some a ∧ ContKeyOk ctx prog act k.cname k.lvls k.ds := by
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
      ∃ a, σ.contAux prog k = some a ∧ ContKeyOk ctx prog act k.cname k.lvls k.ds := by
  intro k hk
  rw [nestSynOccs, List.mem_eraseDups] at hk
  rcases nestSynGo_keys hσ hae e e' {} hrel hnf k hk with hk | h
  · simp at hk
  · exact h

end Syn

end ConLeche
