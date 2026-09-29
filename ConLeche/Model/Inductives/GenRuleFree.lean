module

public import ConLeche.Model.Inductives.GenRuleSyn
public import ConLeche.Semantics.ConstsBound
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Verify.Abstract
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Inductives.ClassGenMinorSyn

public section

/-!
# The stored rule's `ih` pieces name no recursor (lane GENREC-C)

The rule's `ih` pieces — its telescopes' domains, the calls' index and
major arguments — are, up to their free variables, the generator's
pieces of the walked field types (`ClassCtor.tyN`) and the declared field
types (`ClassCtor.tyD`) — and so are the minor premises' inductive
hypotheses in the stored recursor TYPE, which is checked at the
constructors' environment (`classConstOk`: its constants resolve there).
So the rule's pieces name only constants of the constructors'
environment (`CBNF`, constants bound with the free variables forgotten).

`eraseFVars` forgets every free variable (index and annotation); it is a
homomorphism for every operation the generator opens telescopes with,
so two openings of the same term at different variables agree after
it.
-/

namespace ConLeche.Model
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (ConstsBound)
open ConLeche (Env Expr Name Level ConstantVal BinderMeta ClassGen ClassCtor)

/-! ## Forgetting the free variables -/

/-- The one variable every free variable is sent to. -/
@[expose] def F0 : Expr := .fvar 0 (.sort .zero)

/-- Every free variable forgotten. -/
@[expose] def eraseFVars (e : Expr) : Expr := e.replaceFVars fun _ => some F0

/-- **Constants bound, the free variables forgotten.** -/
@[expose] def CBNF (env : Env) (e : Expr) : Prop := ConstsBound env (eraseFVars e)

@[simp] theorem eraseFVars_fvar (i : Nat) (T : Expr) : eraseFVars (.fvar i T) = F0 := rfl

theorem eraseFVars_app (f a : Expr) :
    eraseFVars (.app f a) = .app (eraseFVars f) (eraseFVars a) := rfl

theorem eraseFVars_instantiate1 (v : Expr) :
    ∀ (e : Expr) (k : Nat),
      eraseFVars (e.instantiate1 v k) = (eraseFVars e).instantiate1 (eraseFVars v) k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [Expr.instantiate1, eraseFVars, Expr.replaceFVars]
    split
    · rfl
    · split <;> rfl
  | fvar i T _ => intro k; rfl
  | sort u => intro k; rfl
  | const n us => intro k; rfl
  | lit l => intro k; rfl
  | app f a ihf iha =>
    intro k
    simp only [Expr.instantiate1, eraseFVars, Expr.replaceFVars] at ihf iha ⊢
    rw [ihf, iha]
  | lam t b m iht ihb =>
    intro k
    simp only [Expr.instantiate1, eraseFVars, Expr.replaceFVars] at iht ihb ⊢
    rw [iht, ihb]
  | forallE t b m iht ihb =>
    intro k
    simp only [Expr.instantiate1, eraseFVars, Expr.replaceFVars] at iht ihb ⊢
    rw [iht, ihb]
  | letE t v' b iht ihv ihb =>
    intro k
    simp only [Expr.instantiate1, eraseFVars, Expr.replaceFVars] at iht ihv ihb ⊢
    rw [iht, ihv, ihb]
  | proj s i e ih =>
    intro k
    simp only [Expr.instantiate1, eraseFVars, Expr.replaceFVars] at ih ⊢
    rw [ih]

theorem eraseFVars_mkAppN : ∀ (as : List Expr) (f : Expr),
    eraseFVars (Expr.mkAppN f as) = Expr.mkAppN (eraseFVars f) (as.map eraseFVars)
  | [], _ => rfl
  | a :: as, f => by
    show eraseFVars (Expr.mkAppN (.app f a) as) = _
    rw [eraseFVars_mkAppN as]; rfl

theorem eraseFVars_getAppArgs : ∀ (e : Expr),
    (eraseFVars e).getAppArgs = e.getAppArgs.map eraseFVars := by
  intro e
  induction e with
  | app f a ihf _ =>
    rw [eraseFVars_app]
    simp only [Expr.getAppArgs, List.map_append, ihf, List.map_cons, List.map_nil]
  | _ => rfl

/-! ## `CBNF` -/

theorem constsBound_eraseFVars {env : Env} : ∀ (e : Expr), ConstsBound env e → CBNF env e := by
  intro e
  induction e with
  | fvar i T _ => intro _; simp [CBNF, F0]
  | app f a ihf iha =>
    intro h; rw [ConLeche.Semantics.constsBound_app] at h
    simp only [CBNF, eraseFVars, Expr.replaceFVars, ConLeche.Semantics.constsBound_app] at ihf iha ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam t b m iht ihb =>
    intro h; rw [ConLeche.Semantics.constsBound_lam] at h
    simp only [CBNF, eraseFVars, Expr.replaceFVars, ConLeche.Semantics.constsBound_lam] at iht ihb ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE t b m iht ihb =>
    intro h; rw [ConLeche.Semantics.constsBound_forallE] at h
    simp only [CBNF, eraseFVars, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_forallE] at iht ihb ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h; rw [ConLeche.Semantics.constsBound_letE] at h
    simp only [CBNF, eraseFVars, Expr.replaceFVars, ConLeche.Semantics.constsBound_letE] at iht ihv ihb ⊢
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i e ih =>
    intro h; rw [ConLeche.Semantics.constsBound_proj] at h
    simp only [CBNF, eraseFVars, Expr.replaceFVars, ConLeche.Semantics.constsBound_proj] at ih ⊢
    exact ih h
  | _ => intro h; exact h

theorem eraseFVars_of_erasedEq : ∀ {a b : Expr}, Expr.ErasedEq a b → eraseFVars a = eraseFVars b
  | .bvar i, .bvar j, h => by obtain rfl : i = j := h; rfl
  | .fvar _ _, .fvar _ _, _ => rfl
  | .sort _, .sort _, h => by obtain rfl := h; rfl
  | .const _ _, .const _ _, h => by obtain ⟨rfl, rfl⟩ := h; rfl
  | .lit _, .lit _, h => by obtain rfl := h; rfl
  | .app f a, .app g b, h => by
    show Expr.app (eraseFVars f) (eraseFVars a) = Expr.app (eraseFVars g) (eraseFVars b)
    rw [eraseFVars_of_erasedEq h.1, eraseFVars_of_erasedEq h.2]
  | .lam t b m, .lam t' b' m', h => by
    obtain ⟨rfl, h1, h2⟩ := h
    show Expr.lam (eraseFVars t) (eraseFVars b) m = Expr.lam (eraseFVars t') (eraseFVars b') m
    rw [eraseFVars_of_erasedEq h1, eraseFVars_of_erasedEq h2]
  | .forallE t b m, .forallE t' b' m', h => by
    obtain ⟨rfl, h1, h2⟩ := h
    show Expr.forallE (eraseFVars t) (eraseFVars b) m
      = Expr.forallE (eraseFVars t') (eraseFVars b') m
    rw [eraseFVars_of_erasedEq h1, eraseFVars_of_erasedEq h2]
  | .letE t v b, .letE t' v' b', h => by
    obtain ⟨h1, h2, h3⟩ := h
    show Expr.letE (eraseFVars t) (eraseFVars v) (eraseFVars b)
      = Expr.letE (eraseFVars t') (eraseFVars v') (eraseFVars b')
    rw [eraseFVars_of_erasedEq h1, eraseFVars_of_erasedEq h2, eraseFVars_of_erasedEq h3]
  | .proj s i e, .proj s' i' e', h => by
    obtain ⟨rfl, rfl, h1⟩ := h
    show Expr.proj s i (eraseFVars e) = Expr.proj s i (eraseFVars e')
    rw [eraseFVars_of_erasedEq h1]
  | .bvar _, .fvar _ _, h | .bvar _, .sort _, h | .bvar _, .const _ _, h | .bvar _, .app _ _, h
  | .bvar _, .lam _ _ _, h | .bvar _, .forallE _ _ _, h | .bvar _, .letE _ _ _, h
  | .bvar _, .lit _, h | .bvar _, .proj _ _ _, h => by simp [Expr.ErasedEq] at h
  | .fvar _ _, .bvar _, h | .fvar _ _, .sort _, h | .fvar _ _, .const _ _, h
  | .fvar _ _, .app _ _, h | .fvar _ _, .lam _ _ _, h | .fvar _ _, .forallE _ _ _, h
  | .fvar _ _, .letE _ _ _, h | .fvar _ _, .lit _, h | .fvar _ _, .proj _ _ _, h => by
    simp [Expr.ErasedEq] at h
  | .sort _, .bvar _, h | .sort _, .fvar _ _, h | .sort _, .const _ _, h | .sort _, .app _ _, h
  | .sort _, .lam _ _ _, h | .sort _, .forallE _ _ _, h | .sort _, .letE _ _ _, h
  | .sort _, .lit _, h | .sort _, .proj _ _ _, h => by simp [Expr.ErasedEq] at h
  | .const _ _, .bvar _, h | .const _ _, .fvar _ _, h | .const _ _, .sort _, h
  | .const _ _, .app _ _, h | .const _ _, .lam _ _ _, h | .const _ _, .forallE _ _ _, h
  | .const _ _, .letE _ _ _, h | .const _ _, .lit _, h | .const _ _, .proj _ _ _, h => by
    simp [Expr.ErasedEq] at h
  | .app _ _, .bvar _, h | .app _ _, .fvar _ _, h | .app _ _, .sort _, h
  | .app _ _, .const _ _, h | .app _ _, .lam _ _ _, h | .app _ _, .forallE _ _ _, h
  | .app _ _, .letE _ _ _, h | .app _ _, .lit _, h | .app _ _, .proj _ _ _, h => by
    simp [Expr.ErasedEq] at h
  | .lam _ _ _, .bvar _, h | .lam _ _ _, .fvar _ _, h | .lam _ _ _, .sort _, h
  | .lam _ _ _, .const _ _, h | .lam _ _ _, .app _ _, h | .lam _ _ _, .forallE _ _ _, h
  | .lam _ _ _, .letE _ _ _, h | .lam _ _ _, .lit _, h | .lam _ _ _, .proj _ _ _, h => by
    simp [Expr.ErasedEq] at h
  | .forallE _ _ _, .bvar _, h | .forallE _ _ _, .fvar _ _, h | .forallE _ _ _, .sort _, h
  | .forallE _ _ _, .const _ _, h | .forallE _ _ _, .app _ _, h | .forallE _ _ _, .lam _ _ _, h
  | .forallE _ _ _, .letE _ _ _, h | .forallE _ _ _, .lit _, h
  | .forallE _ _ _, .proj _ _ _, h => by simp [Expr.ErasedEq] at h
  | .letE _ _ _, .bvar _, h | .letE _ _ _, .fvar _ _, h | .letE _ _ _, .sort _, h
  | .letE _ _ _, .const _ _, h | .letE _ _ _, .app _ _, h | .letE _ _ _, .lam _ _ _, h
  | .letE _ _ _, .forallE _ _ _, h | .letE _ _ _, .lit _, h
  | .letE _ _ _, .proj _ _ _, h => by simp [Expr.ErasedEq] at h
  | .lit _, .bvar _, h | .lit _, .fvar _ _, h | .lit _, .sort _, h | .lit _, .const _ _, h
  | .lit _, .app _ _, h | .lit _, .lam _ _ _, h | .lit _, .forallE _ _ _, h
  | .lit _, .letE _ _ _, h | .lit _, .proj _ _ _, h => by simp [Expr.ErasedEq] at h
  | .proj _ _ _, .bvar _, h | .proj _ _ _, .fvar _ _, h | .proj _ _ _, .sort _, h
  | .proj _ _ _, .const _ _, h | .proj _ _ _, .app _ _, h | .proj _ _ _, .lam _ _ _, h
  | .proj _ _ _, .forallE _ _ _, h | .proj _ _ _, .letE _ _ _, h
  | .proj _ _ _, .lit _, h => by simp [Expr.ErasedEq] at h

theorem CBNF_abstract1 {env : Env} (i : Nat) :
    ∀ (e : Expr) (k : Nat), CBNF env (e.abstract1 i k) → CBNF env e := by
  intro e
  induction e with
  | fvar j T _ => intro _ _; simp [CBNF, F0]
  | app f a ihf iha =>
    intro k h
    simp only [CBNF, Expr.abstract1, eraseFVars, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_app] at ihf iha h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam t b m iht ihb =>
    intro k h
    simp only [CBNF, Expr.abstract1, eraseFVars, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_lam] at iht ihb h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE t b m iht ihb =>
    intro k h
    simp only [CBNF, Expr.abstract1, eraseFVars, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_forallE] at iht ihb h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE t v b iht ihv ihb =>
    intro k h
    simp only [CBNF, Expr.abstract1, eraseFVars, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_letE] at iht ihv ihb h ⊢
    exact ⟨iht k h.1, ihv k h.2.1, ihb (k + 1) h.2.2⟩
  | proj s j e ih =>
    intro k h
    simp only [CBNF, Expr.abstract1, eraseFVars, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_proj] at ih h ⊢
    exact ih k h
  | _ => intro k h; exact h

/-- A closed telescope's pieces carry its constants. -/
theorem CBNF_closeTelescope {env : Env} :
    ∀ (nds : List (Expr × BinderMeta)) (i : Nat) (b : Expr),
      CBNF env (ConLeche.closeTelescope nds i b) → (∀ nd ∈ nds, CBNF env nd.1) ∧ CBNF env b
  | [], _, b, h => ⟨(fun _ h' => nomatch h'), h⟩
  | (d, bm) :: nds, i, b, h => by
    simp only [ConLeche.closeTelescope, CBNF, eraseFVars, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_forallE] at h
    have h2 : CBNF env (ConLeche.closeTelescope nds (i + 1) b) :=
      CBNF_abstract1 i _ 0 h.2
    obtain ⟨hn, hb⟩ := CBNF_closeTelescope nds (i + 1) b h2
    refine ⟨fun nd hnd => ?_, hb⟩
    rcases List.mem_cons.mp hnd with rfl | hnd
    · exact h.1
    · exact hn nd hnd

theorem CBNF_mkAppN {env : Env} :
    ∀ (as : List Expr) (f : Expr),
      CBNF env (Expr.mkAppN f as) ↔ CBNF env f ∧ ∀ a ∈ as, CBNF env a
  | [], f => by simp; rfl
  | a :: as, f => by
    have ih := CBNF_mkAppN (env := env) as (.app f a)
    show CBNF env (Expr.mkAppN (.app f a) as) ↔ _
    rw [ih]
    have happ : CBNF env (.app f a) ↔ CBNF env f ∧ CBNF env a := by
      simp only [CBNF, eraseFVars, Expr.replaceFVars, ConLeche.Semantics.constsBound_app]
    rw [happ]
    simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

/-! ## Openings at different variables agree after erasure -/

theorem eraseFVars_forallE (t b : Expr) (m : BinderMeta) :
    eraseFVars (.forallE t b m) = .forallE (eraseFVars t) (eraseFVars b) m := rfl

/-- **Two openings of erasure-equal telescopes** agree after erasure:
their bodies and their variables' domains. -/
theorem openPis_erase :
    ∀ (n : Nat) {e e' : Expr} {d d' : Nat} {fvs fvs' : List Expr} {b b' : Expr},
      eraseFVars e = eraseFVars e' →
      ConLeche.openPisAtFvars n e d = some (fvs, b) →
      ConLeche.openPisAtFvars n e' d' = some (fvs', b') →
      eraseFVars b = eraseFVars b' ∧
        fvs.map (fun x => eraseFVars x.fvarTypeD) = fvs'.map (fun x => eraseFVars x.fvarTypeD)
  | 0, e, e', d, d', fvs, fvs', b, b', he, h, h' => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h h'
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨he, rfl⟩
  | n + 1, .forallE t bd m, .forallE t' bd' m', d, d', fvs, fvs', b, b', he, h, h' => by
    rw [eraseFVars_forallE, eraseFVars_forallE] at he
    injection he with ht hb hm
    simp only [ConLeche.openPisAtFvars] at h h'
    cases hi : ConLeche.openPisAtFvars n (bd.instantiate1 (.fvar d t)) (d + 1) with
    | none => rw [hi] at h; exact nomatch h
    | some o =>
      cases hi' : ConLeche.openPisAtFvars n (bd'.instantiate1 (.fvar d' t')) (d' + 1) with
      | none => rw [hi'] at h'; exact nomatch h'
      | some o' =>
        rw [hi] at h; rw [hi'] at h'
        simp only [Option.some.injEq, Prod.mk.injEq] at h h'
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨rfl, rfl⟩ := h'
        have hins : eraseFVars (bd.instantiate1 (.fvar d t))
            = eraseFVars (bd'.instantiate1 (.fvar d' t')) := by
          rw [eraseFVars_instantiate1, eraseFVars_instantiate1, hb]; rfl
        obtain ⟨h1, h2⟩ := openPis_erase n hins (b := o.2) (b' := o'.2) (fvs := o.1) (fvs' := o'.1)
          (by rw [hi]) (by rw [hi'])
        refine ⟨h1, ?_⟩
        rw [List.map_cons, List.map_cons, h2]
        show eraseFVars t :: _ = eraseFVars t' :: _
        rw [ht]
  | _ + 1, .forallE _ _ _, .bvar _, _, _, _, _, _, _, he, _, h'
  | _ + 1, .forallE _ _ _, .fvar _ _, _, _, _, _, _, _, he, _, h'
  | _ + 1, .forallE _ _ _, .sort _, _, _, _, _, _, _, he, _, h'
  | _ + 1, .forallE _ _ _, .const _ _, _, _, _, _, _, _, he, _, h'
  | _ + 1, .forallE _ _ _, .app _ _, _, _, _, _, _, _, he, _, h'
  | _ + 1, .forallE _ _ _, .lam _ _ _, _, _, _, _, _, _, he, _, h'
  | _ + 1, .forallE _ _ _, .letE _ _ _, _, _, _, _, _, _, he, _, h'
  | _ + 1, .forallE _ _ _, .lit _, _, _, _, _, _, _, he, _, h'
  | _ + 1, .forallE _ _ _, .proj _ _ _, _, _, _, _, _, _, he, _, h' => by
    simp [ConLeche.openPisAtFvars] at h'
  | _ + 1, .bvar _, _, _, _, _, _, _, _, _, h, _ | _ + 1, .fvar _ _, _, _, _, _, _, _, _, _, h, _
  | _ + 1, .sort _, _, _, _, _, _, _, _, _, h, _ | _ + 1, .const _ _, _, _, _, _, _, _, _, _, h, _
  | _ + 1, .app _ _, _, _, _, _, _, _, _, _, h, _ | _ + 1, .lam _ _ _, _, _, _, _, _, _, _, _, h, _
  | _ + 1, .letE _ _ _, _, _, _, _, _, _, _, _, h, _ | _ + 1, .lit _, _, _, _, _, _, _, _, _, h, _
  | _ + 1, .proj _ _ _, _, _, _, _, _, _, _, _, h, _ => by simp [ConLeche.openPisAtFvars] at h

/-- **`targetPiDomsWith` at two variable lists** agrees after erasure. -/
theorem targetPiDomsWith_erase :
    ∀ (xs xs' : List Expr) {t t' : Expr} {ws ws' : List Expr},
      (∀ x ∈ xs, ∃ i T, x = .fvar i T) → (∀ x ∈ xs', ∃ i T, x = .fvar i T) →
      xs.length = xs'.length → eraseFVars t = eraseFVars t' →
      ConLeche.targetPiDomsWith xs t = some ws → ConLeche.targetPiDomsWith xs' t' = some ws' →
      ws.map eraseFVars = ws'.map eraseFVars
  | [], [], t, t', ws, ws', _, _, _, _, h, h' => by
    simp only [ConLeche.targetPiDomsWith, Option.some.injEq] at h h'
    subst h h'; rfl
  | x :: xs, x' :: xs', .forallE d b m, .forallE d' b' m', ws, ws', hx, hx', hl, he, h, h' => by
    rw [eraseFVars_forallE, eraseFVars_forallE] at he
    injection he with hd hb hm
    simp only [ConLeche.targetPiDomsWith] at h h'
    cases hi : ConLeche.targetPiDomsWith xs (b.instantiate1 x) with
    | none => rw [hi] at h; exact nomatch h
    | some w =>
      cases hi' : ConLeche.targetPiDomsWith xs' (b'.instantiate1 x') with
      | none => rw [hi'] at h'; exact nomatch h'
      | some w' =>
        rw [hi] at h; rw [hi'] at h'
        simp only [Functor.map, Option.map_some, Option.some.injEq] at h h'
        subst h h'
        obtain ⟨i, T, rfl⟩ := hx x List.mem_cons_self
        obtain ⟨i', T', rfl⟩ := hx' _ List.mem_cons_self
        have hins : eraseFVars (b.instantiate1 (.fvar i T)) = eraseFVars (b'.instantiate1 (.fvar i' T')) := by
          rw [eraseFVars_instantiate1, eraseFVars_instantiate1, hb]; rfl
        have := targetPiDomsWith_erase xs xs' (fun y hy => hx y (List.mem_cons_of_mem _ hy))
          (fun y hy => hx' y (List.mem_cons_of_mem _ hy)) (by simpa using hl) hins hi hi'
        simp only [List.map_cons, this, hd]
  | [], _ :: _, _, _, _, _, _, _, hl, _, _, _ => nomatch hl
  | _ :: _, [], _, _, _, _, _, _, hl, _, _, _ => nomatch hl
  | _ :: _, _ :: _, .forallE _ _ _, .bvar _, _, _, _, _, _, _, _, h'
  | _ :: _, _ :: _, .forallE _ _ _, .fvar _ _, _, _, _, _, _, _, _, h'
  | _ :: _, _ :: _, .forallE _ _ _, .sort _, _, _, _, _, _, _, _, h'
  | _ :: _, _ :: _, .forallE _ _ _, .const _ _, _, _, _, _, _, _, _, h'
  | _ :: _, _ :: _, .forallE _ _ _, .app _ _, _, _, _, _, _, _, _, h'
  | _ :: _, _ :: _, .forallE _ _ _, .lam _ _ _, _, _, _, _, _, _, _, h'
  | _ :: _, _ :: _, .forallE _ _ _, .letE _ _ _, _, _, _, _, _, _, _, h'
  | _ :: _, _ :: _, .forallE _ _ _, .lit _, _, _, _, _, _, _, _, h'
  | _ :: _, _ :: _, .forallE _ _ _, .proj _ _ _, _, _, _, _, _, _, _, h' => by
    simp [ConLeche.targetPiDomsWith] at h'
  | _ :: _, _ :: _, .bvar _, _, _, _, _, _, _, _, h, _
  | _ :: _, _ :: _, .fvar _ _, _, _, _, _, _, _, _, h, _
  | _ :: _, _ :: _, .sort _, _, _, _, _, _, _, _, h, _
  | _ :: _, _ :: _, .const _ _, _, _, _, _, _, _, _, h, _
  | _ :: _, _ :: _, .app _ _, _, _, _, _, _, _, _, h, _
  | _ :: _, _ :: _, .lam _ _ _, _, _, _, _, _, _, _, h, _
  | _ :: _, _ :: _, .letE _ _ _, _, _, _, _, _, _, _, h, _
  | _ :: _, _ :: _, .lit _, _, _, _, _, _, _, _, h, _
  | _ :: _, _ :: _, .proj _ _ _, _, _, _, _, _, _, _, h, _ => by
    simp [ConLeche.targetPiDomsWith] at h

/-! ## The minor premise, spelled out -/

theorem filterMap_eq_recs (x : ClassCtor) {f : Nat → Option (Nat × Nat × Nat)}
    (hf : ∀ i, f i = match x.kinds.getD i .ordinary with
      | .recursive t tele => some (i, t, tele)
      | .ordinary => none) :
    (List.range x.nF).filterMap f = x.recs := by
  unfold ClassCtor.recs
  congr 1
  funext i
  rw [hf]
  cases x.kinds.getD i .ordinary <;> rfl

/-- **A generated minor premise, spelled out** (`ClassGen.minorTy`): the
telescope of the declared fields and, per recursive field, the `ih`
binder `Π a⃗, motive_t e⃗ (f a⃗)` from the walked field type. -/
theorem minorTy_spec' {g : ClassGen} {c : Nat} {x : ClassCtor} {d : Nat} {T : Expr}
    (h : g.minorTy c x d = some T) :
    ∃ (fvs : List Expr) (res : Expr) (ws : List Expr) (ihs : List (Expr × BinderMeta))
      (concl : Expr),
      ConLeche.openPisAtFvars x.nF x.tyD d = some (fvs, res) ∧
      ConLeche.targetPiDomsWith fvs x.tyN = some ws ∧
      T = ConLeche.closeTelescope (fvs.map g.binder ++ ihs) d concl ∧
      ihs.length = x.recs.length ∧
      ∀ (l : Nat) (q : Nat × Nat × Nat), x.recs[l]? = some q →
        ∃ xs idx, g.ihParts q.2.1 q.2.2 (ws.getD q.1 default) (d + x.nF + l) = some (xs, idx) ∧
          ihs[l]? = some (ConLeche.closeTelescope (xs.map g.binder) (d + x.nF + l)
            (Expr.mkAppN (g.motVar q.2.1) (idx ++ [Expr.mkAppN (fvs.getD q.1 default) xs])), g.bm) := by
  unfold ClassGen.minorTy at h
  obtain ⟨⟨fvs, res⟩, hop, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ws, hws, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  obtain ⟨ihs, hihs, h⟩ := Option.bind_eq_some_iff.mp h
  rw [filterMap_eq_recs x ?hf] at hihs
  case hf => intro i; cases x.kinds.getD i .ordinary <;> rfl
  simp only [Option.pure_def, Option.some.injEq] at h
  refine ⟨fvs, res, ws, ihs, _, hop, hws, h.symm, ?_, fun l q hq => ?_⟩
  · rw [ConLeche.option_mapM_length hihs, List.length_range]
  · have hl : l < x.recs.length := (List.getElem?_eq_some_iff.mp hq).1
    obtain ⟨y, hy, hly⟩ := ConLeche.option_mapM_getElem? hihs l l
      (List.getElem?_range hl)
    have hqd : x.recs.getD l default = q := by rw [List.getD_eq_getElem?_getD, hq]; rfl
    simp only [hqd] at hy
    obtain ⟨⟨xs, idx⟩, hparts, hy⟩ := Option.bind_eq_some_iff.mp hy
    simp only [Option.pure_def, Option.some.injEq] at hy
    exact ⟨xs, idx, hparts, by rw [hly, hy]⟩

/-! ## `CBNF` and the environment crossing -/

theorem eraseFVarTys_idem : ∀ (e : Expr), e.eraseFVarTys.eraseFVarTys = e.eraseFVarTys := by
  intro e
  induction e <;> simp_all [Expr.eraseFVarTys, Expr.replaceFVars]

theorem erasedEq_eraseFVarTys (e : Expr) : Expr.ErasedEq e e.eraseFVarTys :=
  ConLeche.Expr.eraseFVarTys_eq_iff.mp (eraseFVarTys_idem e).symm

theorem constsBound_eraseFVarTys_of_CBNF {env : Env} :
    ∀ (e : Expr), CBNF env e → ConstsBound env e.eraseFVarTys := by
  intro e
  induction e with
  | fvar i T _ => intro _; simp [Expr.eraseFVarTys, Expr.replaceFVars]
  | app f a ihf iha =>
    intro h
    simp only [CBNF, eraseFVars, Expr.eraseFVarTys, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_app] at ihf iha h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam t b m iht ihb =>
    intro h
    simp only [CBNF, eraseFVars, Expr.eraseFVarTys, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_lam] at iht ihb h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE t b m iht ihb =>
    intro h
    simp only [CBNF, eraseFVars, Expr.eraseFVarTys, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_forallE] at iht ihb h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h
    simp only [CBNF, eraseFVars, Expr.eraseFVarTys, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_letE] at iht ihv ihb h ⊢
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i e ih =>
    intro h
    simp only [CBNF, eraseFVars, Expr.eraseFVarTys, Expr.replaceFVars,
      ConLeche.Semantics.constsBound_proj] at ih h ⊢
    exact ih h
  | _ => intro h; exact h

theorem CBNF_of_erasedEq {env : Env} {a b : Expr} (h : Expr.ErasedEq a b) :
    CBNF env a ↔ CBNF env b := by
  unfold CBNF; rw [eraseFVars_of_erasedEq h]

end ConLeche.Model
