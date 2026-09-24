module

public import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Verify.Subst
public import ConLeche.Verify.EnvWF
import ConLeche.Verify.Abstract
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Model.Inductives.NestPosMono

public section

/-!
# The positivity walk's OUTPUT, inverted (lane HOLE2, stage E2a)

`nestPos` (`Kernel/Inductives/Positivity.lean`) returns, besides a
field's kind, the field's NORMAL FORM.  At a flat kind that output has
a shape the walk itself checked:

* `ordinary`: it mentions no member and no hole (`nestOcc … = false`);
* `recursive t`/`reflexive t`: a Π-tower of hole-free domains over the
  member hole `nP + t` applied to the parameter variables and hole-free
  index expressions (`HoleOut`, the `holeApp` and `pi` arms).

The install's tail run (β′) makes every stored constructor its own
normal form (`checkBlockPositivity_inv`: the walk returns `crest` on
`crest`), so the closing of the outputs (`closeTelescope`) IS the
walked term, and every field domain of the walked term is
erasure-equal to its output (`closeTelescope_erasedEq`): the shapes
transfer to the INPUT domains (`HoleIn`), which are what the reading
opens.  This file is purely syntactic; the readings are
`StoredShapes.lean`'s.
-/

namespace ConLeche.Model

open ConLeche (Env Expr Name Level CheckM CheckError NestCtx NestState NestFieldKind NestHole
  BinderMeta nestPos nestFields nestMemberCtor closeTelescope fueledOps openPisAtFvars
  structUsedLater)

/-! ## Erasure-level lemmas -/

/-- The occurrence test ignores what erasure ignores. -/
theorem erasedEq_nestOcc {names : List Name} {lo hi : Nat} :
    ∀ (a b : Expr), Expr.ErasedEq a b → a.nestOcc names lo hi = b.nestOcc names lo hi := by
  intro a
  induction a with
  | bvar i => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | fvar i ty _ => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | sort u => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | const n us => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | lit l => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | app f a ihf iha =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, ihf _ h.1, iha _ h.2]
  | lam ty bd mm iht ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, iht _ h.2.1, ihb _ h.2.2]
  | forallE ty bd mm iht ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, iht _ h.2.1, ihb _ h.2.2]
  | letE ty v bd iht ihv ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, iht _ h.1, ihv _ h.2.1, ihb _ h.2.2]
  | proj s i e ih =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, ih _ h.2.2]

/-- Closing a bvar-bounded term then re-opening it gives it back up to
erasure (`abstract1_instantiate1` without the annotation premise). -/
theorem erasedEq_abstract1_instantiate1 {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      Expr.ErasedEq ((e.abstract1 d k).instantiate1 (.fvar d ty) k) e := by
  intro e
  induction e with
  | bvar i =>
    intro k hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.abstract1, Expr.instantiate1]
    rw [if_neg (by omega), if_neg (by omega)]
    exact Expr.ErasedEq.rfl _
  | fvar idx ty' _ =>
    intro k _
    simp only [Expr.abstract1]
    split
    · rename_i h
      simp only [Expr.instantiate1, if_true]
      exact h.symm
    · exact Expr.ErasedEq.rfl _
  | sort u => intro k _; exact Expr.ErasedEq.rfl _
  | const n us => intro k _; exact Expr.ErasedEq.rfl _
  | lit l => intro k _; exact Expr.ErasedEq.rfl _
  | app f a ihf iha =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihf k hb.1, iha k hb.2⟩
  | lam t b mm iht ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨rfl, iht k hb.1, ihb (k + 1) hb.2⟩
  | forallE t b mm iht ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨rfl, iht k hb.1, ihb (k + 1) hb.2⟩
  | letE t v b iht ihv ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨iht k hb.1.1, ihv k hb.1.2, ihb (k + 1) hb.2⟩
  | proj s i e ih =>
    intro k hb
    simp only [Expr.looseBVarsBounded] at hb
    exact ⟨rfl, rfl, ih k hb⟩

/-- Abstracting a non-hole variable changes no occurrence. -/
theorem nestOcc_abstract1 {names : List Name} {lo hi d : Nat} (hd : ¬ (lo ≤ d ∧ d < hi)) :
    ∀ (e : Expr) (k : Nat), (e.abstract1 d k).nestOcc names lo hi = e.nestOcc names lo hi := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro k
    simp only [Expr.abstract1]
    split
    · rename_i h
      subst h
      simp [Expr.nestOcc, hd]
    · rfl
  | bvar i => intro k; rfl
  | sort u => intro k; rfl
  | const n us => intro k; rfl
  | lit l => intro k; rfl
  | app f a ihf iha => intro k; simp [Expr.abstract1, Expr.nestOcc, ihf, iha]
  | lam t b mm iht ihb => intro k; simp [Expr.abstract1, Expr.nestOcc, iht, ihb]
  | forallE t b mm iht ihb => intro k; simp [Expr.abstract1, Expr.nestOcc, iht, ihb]
  | letE t v b iht ihv ihb => intro k; simp [Expr.abstract1, Expr.nestOcc, iht, ihv, ihb]
  | proj s i e ih => intro k; simp [Expr.abstract1, Expr.nestOcc, ih]

/-- Erasure-equal terms have erasure-equal heads and argument spines. -/
theorem erasedEq_getApp :
    ∀ (e e' : Expr), Expr.ErasedEq e e' →
      Expr.ErasedEq e.getAppFn e'.getAppFn ∧ e.getAppArgs.length = e'.getAppArgs.length ∧
      ∀ (i : Nat) (x x' : Expr), e.getAppArgs[i]? = some x → e'.getAppArgs[i]? = some x' → Expr.ErasedEq x x' := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro e' h
    cases e' with
    | app f' a' =>
      obtain ⟨hf, ha⟩ := h
      obtain ⟨h1, h2, h3⟩ := ihf f' hf
      refine ⟨h1, by simp [Expr.getAppArgs, h2], fun i x x' hx hx' => ?_⟩
      simp only [Expr.getAppArgs] at hx hx'
      by_cases hi : i < f.getAppArgs.length
      · rw [List.getElem?_append_left hi] at hx
        rw [List.getElem?_append_left (by omega)] at hx'
        exact h3 i x x' hx hx'
      · rw [List.getElem?_append_right (by omega)] at hx
        rw [List.getElem?_append_right (by omega)] at hx'
        rw [h2] at hx
        cases hq : i - f'.getAppArgs.length with
        | zero =>
          rw [hq] at hx hx'
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hx'
          subst hx hx'
          exact ha
        | succ q => rw [hq] at hx; simp at hx
    | _ => simp [Expr.ErasedEq] at h
  | _ =>
    intro e' h
    cases e' <;> simp_all [Expr.ErasedEq, Expr.getAppFn, Expr.getAppArgs]

/-! ## The shapes -/

/-- **A member hole applied as the walk's `holeApp` arm checks it**: the
head is hole `t`'s variable, the spine has the member's arity, the first
`nP` arguments are the parameter variables, no argument mentions the
block. -/
@[expose] def HoleAppE (ctx : NestCtx) (t : Nat) (e : Expr) : Prop :=
  (∃ ty, e.getAppFn = .fvar (ctx.nP + t) ty) ∧ t < ctx.names.length ∧
  e.getAppArgs.length = ctx.nP + ctx.nIdxs.getD t 0 ∧
  (∀ p, p < ctx.nP → ∃ ty, e.getAppArgs[p]? = some (.fvar p ty)) ∧
  ∀ x ∈ e.getAppArgs, x.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false

/-- **The walk's output at a member-hole kind**: the hole application,
or a Π over a hole-free domain whose (bvar-closed) opened codomain is
again such an output, closed back. -/
inductive HoleOut (ctx : NestCtx) (t : Nat) : Nat → Expr → Prop
  | app {dep : Nat} {e : Expr} : HoleAppE ctx t e → HoleOut ctx t dep e
  | pi {dep : Nat} {a nb : Expr} {bm : BinderMeta} :
      a.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false → nb.looseBVarsBounded 0 = true →
      HoleOut ctx t (dep + 1) nb → HoleOut ctx t dep (.forallE a (nb.abstract1 dep 0) bm)

/-- **A field domain of member-hole shape**, as the reading opens it:
the hole application under Π binders with hole-free domains, each opened
at its depth. -/
inductive HoleIn (ctx : NestCtx) (t : Nat) : Nat → Expr → Prop
  | app {dep : Nat} {e : Expr} : HoleAppE ctx t e → HoleIn ctx t dep e
  | pi {dep : Nat} {a b : Expr} {bm : BinderMeta} :
      a.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false →
      HoleIn ctx t (dep + 1) (b.instantiate1 (.fvar dep a)) → HoleIn ctx t dep (.forallE a b bm)

theorem HoleAppE.erased {ctx : NestCtx} {t : Nat} {e nd : Expr} (h : HoleAppE ctx t nd)
    (he : Expr.ErasedEq e nd) : HoleAppE ctx t e := by
  obtain ⟨⟨ty, hfn⟩, ht, hlen, hps, hfree⟩ := h
  obtain ⟨h1, h2, h3⟩ := erasedEq_getApp e nd he
  refine ⟨?_, ht, by rw [h2, hlen], fun p hp => ?_, fun x hx => ?_⟩
  · rw [hfn] at h1
    cases hq : e.getAppFn <;> rw [hq] at h1 <;> simp only [Expr.ErasedEq] at h1
    subst h1
    exact ⟨_, rfl⟩
  · obtain ⟨ty, hty⟩ := hps p hp
    have hpl : p < e.getAppArgs.length := by
      rw [h2]; exact (List.getElem?_eq_some_iff.mp hty).1
    obtain ⟨x, hx⟩ : ∃ x, e.getAppArgs[p]? = some x := ⟨_, List.getElem?_eq_getElem hpl⟩
    have := h3 p x _ hx hty
    cases x <;> simp only [Expr.ErasedEq] at this
    subst this
    exact ⟨_, hx⟩
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
    have hil : i < nd.getAppArgs.length := by
      rw [← h2]; exact (List.getElem?_eq_some_iff.mp hi).1
    have hy := List.getElem?_eq_getElem hil
    rw [erasedEq_nestOcc _ _ (h3 i x _ hi hy)]
    exact hfree _ (List.getElem_mem hil)

/-- **An input erasure-equal to a member-hole output has the input
shape.** -/
theorem HoleOut.erased {ctx : NestCtx} {t : Nat} :
    ∀ {dep : Nat} {nd : Expr}, HoleOut ctx t dep nd →
      ∀ {e : Expr}, Expr.ErasedEq e nd → HoleIn ctx t dep e := by
  intro dep nd h
  induction h with
  | app h => intro e he; exact .app (h.erased he)
  | @pi dep a nb bm ha hcl _ ih =>
    intro e he
    cases e with
    | forallE a' b' bm' =>
      obtain ⟨-, ha', hb'⟩ := he
      refine .pi (by rw [erasedEq_nestOcc _ _ ha']; exact ha) (ih ?_)
      exact Expr.ErasedEq.trans
        (Expr.ErasedEq.instantiate1 (v := .fvar dep a') (v' := .fvar dep a) hb' rfl)
        (erasedEq_abstract1_instantiate1 nb 0 hcl)
    | _ => simp [Expr.ErasedEq] at he

/-! ## One field: the walk's run, inverted -/

/-- **The walk's output at a flat kind** (top level, no frame): it is
bvar-closed, hole-free at an ordinary kind, and a member-hole output at
a recursive or reflexive one. -/
theorem nestPos_out {env : Env} (henv : ConLeche.EnvWF env) {ctx : NestCtx} {F : Nat}
    (hpl : ctx.params.length = ctx.nP)
    (hpar : ∀ (p : Nat) (x : Expr), ctx.params[p]? = some x → ∃ ty, x = .fvar p ty) :
    ∀ (fuel dep kb : Nat) (e : Expr) (st : NestState) (k : NestFieldKind) (nd : Expr)
      (st' : NestState),
      nestPos (fueledOps .verified F) env ctx fuel [] dep kb e st = .ok (k, nd, st') →
      k.flat = true → e.looseBVarsBounded 0 = true → ctx.hiAt 0 ≤ dep →
      nd.looseBVarsBounded 0 = true ∧
      (k = .ordinary → nd.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false) ∧
      (∀ t, (k = .recursive t ∨ k = .reflexive t) → HoleOut ctx t dep nd) := by
  intro fuel
  induction fuel with
  | zero =>
    intro dep kb e st k nd st' hrun
    simp [nestPos, throw, throwThe, MonadExceptOf.throw] at hrun
  | succ fuel ih =>
    intro dep kb e st k nd st' hrun hk hcl hhi
    rw [nestPos] at hrun
    cases hw : ConLeche.whnf .verified env F dep e with
    | error err =>
      have hw' : (fueledOps .verified F).whnf env dep e = .error err := hw
      simp [hw', bind, Except.bind] at hrun
    | ok w =>
      have hw' : (fueledOps .verified F).whnf env dep e = .ok w := hw
      simp only [hw', bind, Except.bind, List.length_nil] at hrun
      have hwcl : w.looseBVarsBounded 0 = true := ConLeche.whnf_looseBVars henv F hw hcl
      by_cases hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false
      · rw [if_pos (by simpa using hocc)] at hrun
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl, -⟩ := hrun
        refine ⟨?_, fun _ => ?_, fun t ht => by rcases ht with h | h <;> exact nomatch h⟩
        · split
          · exact hwcl
          · exact hcl
        · split
          · exact hocc
          · rename_i h; simpa using h
      rw [if_neg (by simpa using hocc)] at hrun
      split at hrun
      · -- `pi`
        rename_i a b mb
        by_cases ha : a.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = true
        · rw [if_pos ha] at hrun
          simp [throw, throwThe, MonadExceptOf.throw] at hrun
        rw [if_neg ha] at hrun
        split at hrun
        · simp at hrun
        rename_i v hv
        obtain ⟨k₁, nb, st₁⟩ := v
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl, rfl⟩ := hrun
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hwcl
        have hbcl := ConLeche.looseBVarsBounded_instantiate1 (d := dep) (ty := a) b 0 hwcl.2
        obtain ⟨h1, h2, h3⟩ := ih (dep + 1) (kb + 1) _ st k₁ nb _ hv hk hbcl (by omega)
        have ha' : a.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false := by simpa using ha
        refine ⟨?_, fun ho => ?_, fun t ht => HoleOut.pi ha' h1 (h3 t ht)⟩
        · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
          exact ⟨hwcl.1, ConLeche.looseBVarsBounded_abstract1 nb 0 h1⟩
        · simp only [Expr.nestOcc, ha', Bool.false_or]
          rw [nestOcc_abstract1 (by omega) nb 0]
          exact h2 ho
      · -- a head applied to arguments
        split at hrun
        · rename_i i ty hfn
          by_cases hmem : (decide (ctx.nP ≤ i) && decide (i < ctx.hiAt 0)) = true
          · rw [if_pos hmem] at hrun
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hmem
            by_cases hc : (w.getAppArgs.length == ctx.nP + ctx.nIdxs.getD (i - ctx.nP) 0 &&
                List.take ctx.nP w.getAppArgs == ctx.params &&
                w.getAppArgs.all fun x => !Expr.nestOcc ctx.names ctx.nP (ctx.hiAt 0) x) = true
            · rw [if_pos hc] at hrun
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl, -⟩ := hrun
              simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
                Bool.not_eq_eq_eq_not, Bool.not_true] at hc
              obtain ⟨⟨hlen, htake⟩, hfree⟩ := hc
              have hA : HoleAppE ctx (i - ctx.nP) w := by
                refine ⟨⟨ty, by rw [hfn]; congr 1; omega⟩, ?_, hlen, fun p hp => ?_, hfree⟩
                · simp only [ConLeche.NestCtx.hiAt] at hmem; omega
                · have hq : ctx.params[p]? = w.getAppArgs[p]? := by
                    rw [← htake, List.getElem?_take_of_lt hp]
                  obtain ⟨ty', hty'⟩ : ∃ x, ctx.params[p]? = some x :=
                    ⟨_, List.getElem?_eq_getElem (by omega)⟩
                  obtain ⟨ty'', rfl⟩ := hpar p _ hty'
                  exact ⟨ty'', by rw [← hq, hty']⟩
              refine ⟨hwcl, fun h => ?_, fun t ht => ?_⟩
              · split at h <;> exact nomatch h
              · have htt : t = i - ctx.nP := by
                  split at ht <;> rcases ht with h | h <;>
                    first | exact (NestFieldKind.recursive.inj h).symm
                          | exact (NestFieldKind.reflexive.inj h).symm
                          | exact nomatch h
                subst htt
                exact .app hA
            · rw [if_neg hc] at hrun
              simp [throw, throwThe, MonadExceptOf.throw] at hrun
          · rw [if_neg hmem] at hrun
            by_cases hfr' : (decide (ctx.hiAt 0 ≤ i) && decide (i < ctx.hiAt 0)) = true
            · simp only [Bool.and_eq_true, decide_eq_true_eq] at hfr'
              omega
            · rw [if_neg hfr'] at hrun
              simp [throw, throwThe, MonadExceptOf.throw] at hrun
        · -- `contApp`: no flat kind
          rename_i n us hfn
          by_cases hnm : ctx.names.contains n = true
          · rw [if_pos hnm] at hrun
            simp [throw, throwThe, MonadExceptOf.throw] at hrun
          rw [if_neg hnm] at hrun
          split at hrun
          · simp at hrun
          rename_i v hv
          obtain ⟨k₁, st₁⟩ := v
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -, rfl⟩ := hrun
          rw [nestCont_not_flat hv] at hk
          exact nomatch hk
        · simp [throw, throwThe, MonadExceptOf.throw] at hrun

/-! ## The field telescope -/

/-- **`nestFields`, inverted**: it opens the telescope exactly as
`openPisAtFvars` does (the field variable annotated by the INPUT domain),
each domain through `rec` at its depth. -/
theorem nestFields_inv
    {rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckM (NestFieldKind × Expr × NestState)}
    {base : Nat} {err : CheckError} :
    ∀ (n j : Nat) (cur : Expr) (st : NestState) (ks : List NestFieldKind)
      (nds : List (Expr × BinderMeta)) (res : Expr) (st' : NestState),
      nestFields rec [] base err n j cur st = .ok (ks, nds, res, st') → st'.restart = none →
      ∃ xs, openPisAtFvars n cur (base + j) = some (xs, res) ∧ ks.length = n ∧ nds.length = n ∧
        ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k nd st₁ st₂, ks[i]? = some k ∧ nds[i]?.map (·.1) = some nd ∧
          rec [] (base + j + i) 0 x.fvarTypeD st₁ = .ok (k, nd, st₂)
  | 0, j, cur, st, ks, nds, res, st', h, _ => by
    simp only [nestFields, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨[], by simp [openPisAtFvars], rfl, rfl, fun i x hx => nomatch hx⟩
  | n + 1, j, cur, st, ks, nds, res, st', h, hr => by
    cases cur with
    | forallE a b bm =>
      simp only [nestFields, bind, Except.bind] at h
      split at h
      · simp at h
      rename_i v hv
      obtain ⟨k, nd, st₁⟩ := v
      simp only at h
      split at h
      · rename_i hsome
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, -, rfl⟩ := h
        simp [hr] at hsome
      split at h
      · simp at h
      rename_i v' hv'
      obtain ⟨ks', nds', res', st₂⟩ := v'
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨xs, hop, hkl, hnl, hall⟩ := nestFields_inv n (j + 1) _ st₁ ks' nds' res' st₂ hv' hr
      refine ⟨.fvar (base + j) a :: xs, ?_, by simp [hkl], by simp [hnl], ?_⟩
      · simp only [openPisAtFvars]
        rw [show base + j + 1 = base + (j + 1) by omega, hop]
      · intro i x hx
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          exact ⟨k, nd, st, st₁, rfl, rfl, by simpa [Expr.fvarTypeD] using hv⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx
          obtain ⟨k', nd', s1, s2, h1, h2, h3⟩ := hall i x hx
          refine ⟨k', nd', s1, s2, by simpa using h1, by simpa using h2, ?_⟩
          rw [show base + j + (i + 1) = base + (j + 1) + i by omega]
          exact h3
    | _ => simp [nestFields, throw, throwThe, MonadExceptOf.throw] at h

/-- A closed telescope of closed pieces is closed. -/
theorem closeTelescope_closed :
    ∀ (nds : List (Expr × BinderMeta)) (i : Nat) (body : Expr),
      (∀ p ∈ nds, p.1.looseBVarsBounded 0 = true) → body.looseBVarsBounded 0 = true →
      (closeTelescope nds i body).looseBVarsBounded 0 = true
  | [], _, _, _, hb => hb
  | (dom, bm) :: nds, i, body, h, hb => by
    simp only [closeTelescope, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨h _ List.mem_cons_self, ConLeche.looseBVarsBounded_abstract1 _ 0
      (closeTelescope_closed nds (i + 1) body (fun p hp => h p (List.mem_cons_of_mem _ hp)) hb)⟩

/-- **A telescope erasure-equal to the closing of its outputs**: every
opened domain is erasure-equal to its output. -/
theorem closeTelescope_erasedEq :
    ∀ (n : Nat) (e : Expr) (d : Nat) (xs : List Expr) (rest : Expr)
      (nds : List (Expr × BinderMeta)),
      openPisAtFvars n e d = some (xs, rest) → nds.length = n →
      (∀ p ∈ nds, p.1.looseBVarsBounded 0 = true) → rest.looseBVarsBounded 0 = true →
      Expr.ErasedEq (closeTelescope nds d rest) e →
      ∀ (i : Nat) (x nd : Expr), xs[i]? = some x → nds[i]?.map (·.1) = some nd →
        Expr.ErasedEq x.fvarTypeD nd
  | 0, e, d, xs, rest, nds, hop, _, _, _, _, i, x, nd, hx, _ => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    exact nomatch hx
  | n + 1, e, d, xs, rest, nds, hop, hl, hcl, hrc, he, i, x, nd, hx, hnd => by
    match e, nds, hop, hl with
    | .forallE dom body mb, (nd0, bm0) :: nds', hop, hl =>
      simp only [openPisAtFvars] at hop
      split at hop
      · rename_i xs' r hop'
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        simp only [closeTelescope] at he
        obtain ⟨-, hdom, hbody⟩ := he
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at hnd
          subst hx hnd
          exact Expr.ErasedEq.symm hdom
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx hnd
          have hcl' : ∀ p ∈ nds', p.1.looseBVarsBounded 0 = true :=
            fun p hp => hcl p (List.mem_cons_of_mem _ hp)
          have hC := closeTelescope_closed nds' (d + 1) r hcl' hrc
          refine closeTelescope_erasedEq n _ (d + 1) xs' r nds' hop' (by simpa using hl) hcl'
            hrc ?_ i x nd hx hnd
          exact Expr.ErasedEq.trans
            (Expr.ErasedEq.symm (erasedEq_abstract1_instantiate1 (d := d) (ty := dom) _ 0 hC))
            (Expr.ErasedEq.instantiate1 hbody rfl)
      · exact nomatch hop

/-! ## One constructor -/

/-- **`nestMemberCtor`, inverted**: the fields' walk, the normal form it
closes, U4 (no later field and not the result uses a recursive or
reflexive field) and the result's hole-free indices. -/
theorem nestMemberCtor_inv {ops : ConLeche.CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {nF : Nat} {crest : Expr} {st : NestState} {ks : List NestFieldKind} {tyN : Expr}
    {st' : NestState}
    (h : nestMemberCtor ops env ctx nF crest st = .ok (ks, tyN, st')) :
    ∃ (err : CheckError) (nds : List (Expr × BinderMeta)) (cur : Expr),
      nestFields (nestPos ops env ctx 1024) [] (ctx.hiAt 0) err nF 0 crest st
        = .ok (ks, nds, cur, st') ∧ st'.restart = none ∧
      tyN = closeTelescope nds (ctx.hiAt 0) cur ∧
      (∀ i, i < nF → (∃ t, ks.getD i .ordinary = .recursive t ∨
          ks.getD i .ordinary = .reflexive t) → structUsedLater tyN 0 i = false) ∧
      ∀ a ∈ cur.getAppArgs.drop ctx.nP, a.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false := by
  simp only [nestMemberCtor, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i v hv
  obtain ⟨ks₁, nds, cur, st₁⟩ := v
  simp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hres
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hany
  split at h
  · rename_i hresult
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨_, nds, cur, hv, by simpa using hres, rfl, fun i hi ⟨t, ht⟩ => ?_, ?_⟩
    · simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, not_exists, not_and] at hany
      cases hu : structUsedLater (closeTelescope nds (ctx.hiAt 0) cur) 0 i
      · rfl
      · have := hany i hi
        rcases ht with ht | ht <;> rw [ht] at this <;> exact absurd hu (by simpa using this)
    · simp only [Bool.and_eq_true, List.all_eq_true] at hresult
      intro a ha
      simpa using hresult.2 a ha
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **A stored constructor that is its own positivity normal form, field
by field** (the (β′) run): its telescope opens at the walk's depth; the
result's index expressions are hole-free; every field domain is hole-free
at an ordinary kind, or of member-hole shape (`HoleIn`) with no later
field and not the result using it (U4). -/
theorem storedWalk_fields {env : Env} (henv : ConLeche.EnvWF env) {ctx : NestCtx} {F : Nat}
    (hpl : ctx.params.length = ctx.nP)
    (hpar : ∀ (p : Nat) (x : Expr), ctx.params[p]? = some x → ∃ ty, x = .fvar p ty)
    {nF : Nat} {crest : Expr} {st₀ st₁ : NestState} {ks : List NestFieldKind}
    (hcl : crest.looseBVarsBounded 0 = true)
    (hm : nestMemberCtor (fueledOps .verified F) env ctx nF crest st₀ = .ok (ks, crest, st₁))
    (hks : ∀ k ∈ ks, k.flat = true) :
    ∃ (xs : List Expr) (rest : Expr), openPisAtFvars nF crest (ctx.hiAt 0) = some (xs, rest) ∧
      (∀ a ∈ rest.getAppArgs.drop ctx.nP, a.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false) ∧
      ∀ (i : Nat) (x : Expr), xs[i]? = some x →
        x.fvarTypeD.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false ∨
        ∃ t, HoleIn ctx t (ctx.hiAt 0 + i) x.fvarTypeD ∧ structUsedLater crest 0 i = false := by
  obtain ⟨err, nds, cur, hf, hr, htyN, hU4, hres⟩ := nestMemberCtor_inv hm
  obtain ⟨xs, hop, hkl, hnl, hall⟩ := nestFields_inv nF 0 crest st₀ ks nds cur st₁ hf hr
  rw [Nat.add_zero] at hop
  obtain ⟨hcurcl, hxcl⟩ := ConLeche.Verify.openPisAtFvars_bounded nF hop hcl
  have hxl : xs.length = nF := ConLeche.Verify.openPisAtFvars_length nF hop
  -- every field's run, read off
  have hfield : ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k nd,
      ks[i]? = some k ∧ nds[i]?.map (·.1) = some nd ∧ nd.looseBVarsBounded 0 = true ∧
      (k = .ordinary → nd.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false) ∧
      (∀ t, (k = .recursive t ∨ k = .reflexive t) → HoleOut ctx t (ctx.hiAt 0 + i) nd) ∧
      k.flat = true := by
    intro i x hx
    obtain ⟨k, nd, s1, s2, hk, hnd, hrun⟩ := hall i x hx
    rw [Nat.add_zero] at hrun
    have hkf := hks k (List.mem_of_getElem? hk)
    obtain ⟨h1, h2, h3⟩ := nestPos_out henv hpl hpar 1024 _ 0 _ s1 k nd s2 hrun hkf
      (hxcl x (List.mem_of_getElem? hx)) (by omega)
    exact ⟨k, nd, hk, hnd, h1, h2, h3, hkf⟩
  have hndcl : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hp
    have hil : i < xs.length := by
      rw [hxl, ← hnl]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨k, nd, -, hnd, hcl', -⟩ := hfield i _ (List.getElem?_eq_getElem hil)
    rw [hi, Option.map_some, Option.some.injEq] at hnd
    rw [hnd]; exact hcl'
  refine ⟨xs, cur, hop, hres, fun i x hx => ?_⟩
  obtain ⟨k, nd, hk, hnd, -, hord, hhole, hkf⟩ := hfield i x hx
  have hE : Expr.ErasedEq x.fvarTypeD nd :=
    closeTelescope_erasedEq nF crest (ctx.hiAt 0) xs cur nds hop hnl hndcl hcurcl
      (by rw [← htyN]; exact Expr.ErasedEq.rfl _) i x nd hx hnd
  have hi : i < nF := by rw [← hxl]; exact (List.getElem?_eq_some_iff.mp hx).1
  have hkD : ks.getD i .ordinary = k := by
    rw [List.getD_eq_getElem?_getD, hk]; rfl
  cases k with
  | ordinary => exact Or.inl (by rw [erasedEq_nestOcc _ _ hE]; exact hord rfl)
  | recursive t =>
    refine Or.inr ⟨t, (hhole t (Or.inl rfl)).erased hE, ?_⟩
    rw [htyN] at hU4 ⊢
    exact hU4 i hi ⟨t, Or.inl hkD⟩
  | reflexive t =>
    refine Or.inr ⟨t, (hhole t (Or.inr rfl)).erased hE, ?_⟩
    rw [htyN] at hU4 ⊢
    exact hU4 i hi ⟨t, Or.inr hkD⟩
  | inProgress => exact absurd hkf (by decide)
  | nested q r => exact absurd hkf (by simp [NestFieldKind.flat])

end ConLeche.Model
