import Setlec.TTVerify.SubstAlgebra

/-!
# Weakening (with lifting) and substitution for `HasType`

The two derivation-level lemmas of the substitution algebra:

* `HasType.weakenN` / `HasType.weakenHead`: inserting binders into the
  context, `Γ ⊢ e : A → (B :: Γ) ⊢ e.lift : A.lift` at the head and its
  cut-generalized form;
* `HasType.instN` / `HasType.instantiate`: substitution,
  `(A :: Γ) ⊢ b : B → Γ ⊢ a : A → Γ ⊢ b.inst a : B.inst a`.

Both go by one induction over the derivation, generalized over a
context-transformation relation (`LiftCtx`, `InstCtx`) in the style of
lean4lean's `Ctx.LiftN`/`Ctx.InstN`: under a binder the cut grows by
one and the binder's own type is transformed at the old cut, which is
exactly what the relations' `succ` constructors record.

**Why this lives on the bridge side and not in `Setlec/TT/*`.**  The
layer deliberately has *no syntactic metatheory* — that is a design
property it advertises (`Setlec/TT/Subst.lean`), and the bridge's
substitution burden is a handful of lemmas against lean4lean's ~123.
Like `Setlec/TTVerify/Weaken.lean` and `Setlec/TTVerify/Inversion.lean`
these are bridge infrastructure, filed here so they stay marked as a
bridge need rather than quietly becoming layer metatheory.

**Reach for the object-level route first.**  The layer *internalizes*
substitution through abstraction and application, and that route is
preferred wherever it works: to move a `Deq` from an open context to a
closed instance, apply `lam` (which needs no domain premise), then the
`app` rule at the closed arguments — the rule's own `B.inst a` performs
the instantiation object-level in the type — then `symm` twice to
restore the subject.  That trick has already made one use of this file
unnecessary before it existed.  These lemmas are for the residue where
the object-level route does not reach (e.g. when the *type* being
transported is not itself the subject of a rule); they must not become
the default hammer that stops that search.

**Gotcha for `HasType` inductions** (recorded in
`Setlec/TTVerify/Weaken.lean` and repeated because it bites): do not
use `constructor` — `conv`'s conclusion `HasType Γ t B` unifies with
every goal, so it gets selected in all 32 cases.  Every case below
names its constructor.
-/

namespace Setlec.TT

open VExpr

/-! ## The context transformations -/

/-- `LiftCtx n k Γ Γ'`: the context `Γ'` is `Γ` with `n` new entries
inserted at position `k`; the `k` entries below the insertion point are
lifted, each at its own depth.  (Transpose of lean4lean's
`Ctx.LiftN`.) -/
inductive LiftCtx (n : Nat) : Nat → List VExpr → List VExpr → Prop where
  | zero (As : List VExpr) {Γ : List VExpr} (h : As.length = n) :
      LiftCtx n 0 Γ (As ++ Γ)
  | succ {k : Nat} {Γ Γ' : List VExpr} (A : VExpr) :
      LiftCtx n k Γ Γ' → LiftCtx n (k + 1) (A :: Γ) (A.liftN n k :: Γ')

/-- `InstCtx Γ₀ v A₀ k Γ Γ'`: the context `Γ` is `Γ'` with an entry
`A₀` inserted at position `k` (so `Γ'` ends in `Γ₀`, the context that
types the substituted value `v`); the `k` entries below the cut are
instantiated, each at its own depth. -/
inductive InstCtx (Γ₀ : List VExpr) (v A₀ : VExpr) :
    Nat → List VExpr → List VExpr → Prop where
  | zero : InstCtx Γ₀ v A₀ 0 (A₀ :: Γ₀) Γ₀
  | succ {k : Nat} {Γ Γ' : List VExpr} (B : VExpr) :
      InstCtx Γ₀ v A₀ k Γ Γ' →
      InstCtx Γ₀ v A₀ (k + 1) (B :: Γ) (B.inst v k :: Γ')

/-- Below the cut, lookups answer with a lift at the entry's own
depth. -/
theorem LiftCtx.getElem?_lt {n k : Nat} {Γ Γ' : List VExpr}
    (H : LiftCtx n k Γ Γ') {i : Nat} {A : VExpr} (hik : i < k)
    (h : Γ[i]? = some A) : Γ'[i]? = some (A.liftN n (k - 1 - i)) := by
  induction H generalizing i with
  | zero As hAs => omega
  | @succ k Γ Γ' B H ih =>
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at h
      cases h
      rw [List.getElem?_cons_zero, show k + 1 - 1 - 0 = k by omega]
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      rw [List.getElem?_cons_succ, show k + 1 - 1 - (i + 1) = k - 1 - i by omega]
      exact ih (by omega) h

/-- At or above the cut, lookups answer unchanged, `n` places later. -/
theorem LiftCtx.getElem?_ge {n k : Nat} {Γ Γ' : List VExpr}
    (H : LiftCtx n k Γ Γ') {i : Nat} {A : VExpr} (hik : k ≤ i)
    (h : Γ[i]? = some A) : Γ'[i + n]? = some A := by
  induction H generalizing i with
  | @zero As Γ hAs =>
    rw [List.getElem?_append_right (by omega),
      show i + n - As.length = i by omega]
    exact h
  | @succ k Γ Γ' B H ih =>
    cases i with
    | zero => omega
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      rw [show i + 1 + n = i + n + 1 by omega, List.getElem?_cons_succ]
      exact ih (by omega) h

/-- Below the cut, lookups answer with an instantiation at the entry's
own depth. -/
theorem InstCtx.getElem?_lt {Γ₀ : List VExpr} {v A₀ : VExpr} {k : Nat}
    {Γ Γ' : List VExpr} (H : InstCtx Γ₀ v A₀ k Γ Γ') {i : Nat} {A : VExpr}
    (hik : i < k) (h : Γ[i]? = some A) :
    Γ'[i]? = some (A.inst v (k - 1 - i)) := by
  induction H generalizing i with
  | zero => omega
  | @succ k Γ Γ' B H ih =>
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at h
      cases h
      rw [List.getElem?_cons_zero, show k + 1 - 1 - 0 = k by omega]
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      rw [List.getElem?_cons_succ, show k + 1 - 1 - (i + 1) = k - 1 - i by omega]
      exact ih (by omega) h

/-- At the cut sits the type of the substituted value. -/
theorem InstCtx.getElem?_eq {Γ₀ : List VExpr} {v A₀ : VExpr} {k : Nat}
    {Γ Γ' : List VExpr} (H : InstCtx Γ₀ v A₀ k Γ Γ') : Γ[k]? = some A₀ := by
  induction H with
  | zero => rfl
  | succ B H ih => exact ih

/-- Above the cut, lookups answer unchanged, one place earlier. -/
theorem InstCtx.getElem?_gt {Γ₀ : List VExpr} {v A₀ : VExpr} {k : Nat}
    {Γ Γ' : List VExpr} (H : InstCtx Γ₀ v A₀ k Γ Γ') {i : Nat} {A : VExpr}
    (hik : k < i) (h : Γ[i]? = some A) : Γ'[i - 1]? = some A := by
  induction H generalizing i with
  | zero =>
    cases i with
    | zero => omega
    | succ i => rw [List.getElem?_cons_succ] at h; exact h
  | @succ k Γ Γ' B H ih =>
    cases i with
    | zero => omega
    | succ i =>
      cases i with
      | zero => omega
      | succ i =>
        rw [List.getElem?_cons_succ] at h
        rw [show i + 1 + 1 - 1 = (i + 1 - 1) + 1 by omega,
          List.getElem?_cons_succ]
        exact ih (by omega) h

/-- The instantiated part of an `InstCtx` context is a plain prefix
over `Γ₀`: forgetting what the entries are gives a head insertion. -/
theorem InstCtx.toLiftCtx {Γ₀ : List VExpr} {v A₀ : VExpr} {k : Nat}
    {Γ Γ' : List VExpr} (H : InstCtx Γ₀ v A₀ k Γ Γ') :
    LiftCtx k 0 Γ₀ Γ' := by
  induction H with
  | zero => exact .zero [] rfl
  | @succ k Γ Γ' B H ih =>
    cases ih with
    | zero As hAs => exact .zero (B.inst v k :: As) (by simp [hAs])

/-! ## Weakening with lifting -/

/-- **Binder weakening.**  Inserting `n` binders at depth `k` preserves
every derivation, lifting subject and type at the cut. -/
theorem HasType.weakenN : ∀ {Γ : List VExpr} {e A : VExpr}, Γ ⊢ e : A →
    ∀ {n k : Nat} {Γ' : List VExpr}, LiftCtx n k Γ Γ' →
      Γ' ⊢ e.liftN n k : A.liftN n k := by
  intro Γ e A h
  induction h with
  | @bvar Γ i A hi =>
    intro n k Γ' H
    by_cases hik : i < k
    · have h1 := HasType.bvar (H.getElem?_lt hik hi)
      rw [liftN_liftN_comm A (Nat.zero_le (k - 1 - i)) (i + 1) n,
        show k - 1 - i + (i + 1) = k by omega] at h1
      simpa only [liftN_bvar, if_pos hik] using h1
    · rw [liftN_liftN_absorb A (Nat.zero_le k) (show k ≤ 0 + (i + 1) by omega) n,
        show i + 1 + n = i + n + 1 by omega]
      simpa only [liftN_bvar, if_neg hik] using
        HasType.bvar (H.getElem?_ge (by omega) hi)
  | sort => intro n k Γ' H; exact .sort
  | const =>
    intro n k Γ' H
    rw [BConst.liftN_type]
    exact .const
  | pi _ _ ihA ihB => intro n k Γ' H; exact .pi (ihA H) (ihB (H.succ _))
  | lam _ ih => intro n k Γ' H; exact .lam (ih (H.succ _))
  | @app Γ f a A B _ _ ihf iha =>
    intro n k Γ' H
    rw [liftN_inst_comm B (Nat.zero_le k) a n, Nat.sub_zero]
    exact .app (ihf H) (iha H)
  | @letE Γ ty val body B u _ _ _ ihty ihval ihbody =>
    intro n k Γ' H
    have h3 := ihbody H
    rw [liftN_inst_comm body (Nat.zero_le k) val n, Nat.sub_zero] at h3
    exact .letE (ihty H) (ihval H) h3
  | eqType => intro n k Γ' H; exact .eqType
  | conv _ _ iht ihp => intro n k Γ' H; exact .conv (iht H) (ihp H)
  | refl => intro n k Γ' H; exact .refl
  | symm _ ih => intro n k Γ' H; exact .symm (ih H)
  | trans _ _ ih1 ih2 => intro n k Γ' H; exact .trans (ih1 H) (ih2 H)
  | congrApp _ _ ih1 ih2 => intro n k Γ' H; exact .congrApp (ih1 H) (ih2 H)
  | congrLam _ _ ih1 ih2 =>
    intro n k Γ' H; exact .congrLam (ih1 H) (ih2 (H.succ _))
  | congrPi _ _ ih1 ih2 =>
    intro n k Γ' H; exact .congrPi (ih1 H) (ih2 (H.succ _))
  | congrProj _ ih => intro n k Γ' H; exact .congrProj (ih H)
  | congrEq _ _ ih1 ih2 => intro n k Γ' H; exact .congrEq (ih1 H) (ih2 H)
  | @beta Γ T A a b _ iha =>
    intro n k Γ' H
    simp only [liftN_prf, liftN_eqE, liftN_app, liftN_lam]
    rw [liftN_inst_comm b (Nat.zero_le k) a n, Nat.sub_zero]
    exact .beta (iha H)
  | @zeta Γ T ty val body =>
    intro n k Γ' H
    simp only [liftN_prf, liftN_eqE, liftN_letE]
    rw [liftN_inst_comm body (Nat.zero_le k) val n, Nat.sub_zero]
    exact .zeta
  | @eta Γ T A B f _ ihf =>
    intro n k Γ' H
    simp only [liftN_prf, liftN_eqE, liftN_lam, liftN_app, liftN_bvar,
      if_pos (show (0 : Nat) < k + 1 by omega)]
    rw [← liftN_liftN_comm f (Nat.zero_le k) 1 n]
    exact .eta (ihf H)
  | @funext Γ T T' A B B' f g p _ _ _ ihf ihg ihp =>
    intro n k Γ' H
    have h3 := ihp (H.succ _)
    simp only [liftN_eqE, liftN_app, liftN_bvar,
      if_pos (show (0 : Nat) < k + 1 by omega)] at h3
    rw [← liftN_liftN_comm f (Nat.zero_le k) 1 n,
      ← liftN_liftN_comm g (Nat.zero_le k) 1 n] at h3
    exact .funext (ihf H) (ihg H) h3
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    intro n k Γ' H; exact .proofIrrel (ih1 H) (ih2 H) (ih3 H)
  | natRecZero _ _ _ ihM ihz ihs =>
    intro n k Γ' H
    have h3 := ihs H
    rw [liftN_natStepT] at h3
    exact .natRecZero (ihM H) (ihz H) h3
  | natRecSucc _ _ _ _ ihM ihz ihs ihn =>
    intro n k Γ' H
    have h3 := ihs H
    rw [liftN_natStepT] at h3
    exact .natRecSucc (ihM H) (ihz H) h3 (ihn H)
  | punitRecUnit _ _ ih1 ih2 =>
    intro n k Γ' H; exact .punitRecUnit (ih1 H) (ih2 H)
  | punitEta _ _ ih1 ih2 => intro n k Γ' H; exact .punitEta (ih1 H) (ih2 H)
  | projFst _ _ _ ih1 ih2 ih3 =>
    intro n k Γ' H; exact .projFst (ih1 H) (ih2 H) (ih3 H)
  | projSnd _ _ _ ih1 ih2 ih3 =>
    intro n k Γ' H; exact .projSnd (ih1 H) (ih2 H) (ih3 H)
  | projFstMk _ _ _ _ ih1 ih2 ih3 ih4 =>
    intro n k Γ' H; exact .projFstMk (ih1 H) (ih2 H) (ih3 H) (ih4 H)
  | projSndMk _ _ _ _ ih1 ih2 ih3 ih4 =>
    intro n k Γ' H; exact .projSndMk (ih1 H) (ih2 H) (ih3 H) (ih4 H)
  | psigmaEta _ _ _ ih1 ih2 ih3 =>
    intro n k Γ' H; exact .psigmaEta (ih1 H) (ih2 H) (ih3 H)
  | quotLiftMk _ _ _ _ _ _ ihA ihr ihB ihf ihh iha =>
    intro n k Γ' H
    have h2 := ihr H
    have h4 := ihf H
    have h5 := ihh H
    rw [liftN_relT] at h2
    rw [liftN_arrow] at h4
    rw [liftN_quotInvT] at h5
    exact .quotLiftMk (ihA H) h2 (ihB H) h4 h5 (iha H)

/-- Weakening at the head of the context: a fresh innermost binder
shifts every de Bruijn index by one. -/
theorem HasType.weakenHead {Γ : List VExpr} {e A : VExpr} (B : VExpr)
    (h : Γ ⊢ e : A) : B :: Γ ⊢ e.lift : A.lift :=
  h.weakenN (.zero [B] rfl)

/-! ## Substitution -/

/-- **Substitution, cut-generalized.**  Substituting a well-typed value
for the context entry at depth `k` preserves every derivation. -/
theorem HasType.instN {Γ₀ : List VExpr} {v A₀ : VExpr} (hv : Γ₀ ⊢ v : A₀) :
    ∀ {Γ : List VExpr} {b B : VExpr}, Γ ⊢ b : B →
    ∀ {k : Nat} {Γ' : List VExpr}, InstCtx Γ₀ v A₀ k Γ Γ' →
      Γ' ⊢ b.inst v k : B.inst v k := by
  intro Γ b B h
  induction h with
  | @bvar Γ i A hi =>
    intro k Γ' H
    by_cases hik : i < k
    · rw [inst_liftN_comm A (show 0 + (i + 1) ≤ k by omega) v,
        show k - (i + 1) = k - 1 - i by omega]
      simpa only [inst_bvar, if_pos hik] using
        HasType.bvar (H.getElem?_lt hik hi)
    · by_cases hik2 : i = k
      · have hA0 : A = A₀ := by
          rw [hik2] at hi
          exact Option.some.inj (hi.symm.trans H.getElem?_eq)
        subst hA0
        rw [hik2, inst_liftN_absorb A (Nat.zero_le k) (show k ≤ 0 + k by omega) v]
        simp only [inst_bvar, if_neg (show ¬ k < k by omega)]
        exact hv.weakenN H.toLiftCtx
      · rw [inst_liftN_absorb A (Nat.zero_le k) (show k ≤ 0 + i by omega) v]
        have h1 := HasType.bvar (H.getElem?_gt (by omega) hi)
        rw [show i - 1 + 1 = i by omega] at h1
        simpa only [inst_bvar, if_neg hik, if_neg hik2] using h1
  | sort => intro k Γ' H; exact .sort
  | const =>
    intro k Γ' H
    rw [BConst.inst_type]
    exact .const
  | pi _ _ ihA ihB => intro k Γ' H; exact .pi (ihA H) (ihB (H.succ _))
  | lam _ ih => intro k Γ' H; exact .lam (ih (H.succ _))
  | @app Γ f a A B _ _ ihf iha =>
    intro k Γ' H
    rw [inst_inst_comm B (Nat.zero_le k) v a, Nat.sub_zero]
    exact .app (ihf H) (iha H)
  | @letE Γ ty val body B u _ _ _ ihty ihval ihbody =>
    intro k Γ' H
    have h3 := ihbody H
    rw [inst_inst_comm body (Nat.zero_le k) v val, Nat.sub_zero] at h3
    exact .letE (ihty H) (ihval H) h3
  | eqType => intro k Γ' H; exact .eqType
  | conv _ _ iht ihp => intro k Γ' H; exact .conv (iht H) (ihp H)
  | refl => intro k Γ' H; exact .refl
  | symm _ ih => intro k Γ' H; exact .symm (ih H)
  | trans _ _ ih1 ih2 => intro k Γ' H; exact .trans (ih1 H) (ih2 H)
  | congrApp _ _ ih1 ih2 => intro k Γ' H; exact .congrApp (ih1 H) (ih2 H)
  | congrLam _ _ ih1 ih2 =>
    intro k Γ' H; exact .congrLam (ih1 H) (ih2 (H.succ _))
  | congrPi _ _ ih1 ih2 =>
    intro k Γ' H; exact .congrPi (ih1 H) (ih2 (H.succ _))
  | congrProj _ ih => intro k Γ' H; exact .congrProj (ih H)
  | congrEq _ _ ih1 ih2 => intro k Γ' H; exact .congrEq (ih1 H) (ih2 H)
  | @beta Γ T A a b _ iha =>
    intro k Γ' H
    simp only [inst_prf, inst_eqE, inst_app, inst_lam]
    rw [inst_inst_comm b (Nat.zero_le k) v a, Nat.sub_zero]
    exact .beta (iha H)
  | @zeta Γ T ty val body =>
    intro k Γ' H
    simp only [inst_prf, inst_eqE, inst_letE]
    rw [inst_inst_comm body (Nat.zero_le k) v val, Nat.sub_zero]
    exact .zeta
  | @eta Γ T A B f _ ihf =>
    intro k Γ' H
    simp only [inst_prf, inst_eqE, inst_lam, inst_app, inst_bvar,
      if_pos (show (0 : Nat) < k + 1 by omega)]
    rw [inst_liftN_comm f (show 0 + 1 ≤ k + 1 by omega) v,
      Nat.add_sub_cancel]
    exact .eta (ihf H)
  | @funext Γ T T' A B B' f g p _ _ _ ihf ihg ihp =>
    intro k Γ' H
    have h3 := ihp (H.succ _)
    simp only [inst_eqE, inst_app, inst_bvar,
      if_pos (show (0 : Nat) < k + 1 by omega)] at h3
    rw [inst_liftN_comm f (show 0 + 1 ≤ k + 1 by omega) v,
      inst_liftN_comm g (show 0 + 1 ≤ k + 1 by omega) v,
      Nat.add_sub_cancel] at h3
    exact .funext (ihf H) (ihg H) h3
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    intro k Γ' H; exact .proofIrrel (ih1 H) (ih2 H) (ih3 H)
  | natRecZero _ _ _ ihM ihz ihs =>
    intro k Γ' H
    have h3 := ihs H
    rw [inst_natStepT] at h3
    exact .natRecZero (ihM H) (ihz H) h3
  | natRecSucc _ _ _ _ ihM ihz ihs ihn =>
    intro k Γ' H
    have h3 := ihs H
    rw [inst_natStepT] at h3
    exact .natRecSucc (ihM H) (ihz H) h3 (ihn H)
  | punitRecUnit _ _ ih1 ih2 =>
    intro k Γ' H; exact .punitRecUnit (ih1 H) (ih2 H)
  | punitEta _ _ ih1 ih2 => intro k Γ' H; exact .punitEta (ih1 H) (ih2 H)
  | projFst _ _ _ ih1 ih2 ih3 =>
    intro k Γ' H; exact .projFst (ih1 H) (ih2 H) (ih3 H)
  | projSnd _ _ _ ih1 ih2 ih3 =>
    intro k Γ' H; exact .projSnd (ih1 H) (ih2 H) (ih3 H)
  | projFstMk _ _ _ _ ih1 ih2 ih3 ih4 =>
    intro k Γ' H; exact .projFstMk (ih1 H) (ih2 H) (ih3 H) (ih4 H)
  | projSndMk _ _ _ _ ih1 ih2 ih3 ih4 =>
    intro k Γ' H; exact .projSndMk (ih1 H) (ih2 H) (ih3 H) (ih4 H)
  | psigmaEta _ _ _ ih1 ih2 ih3 =>
    intro k Γ' H; exact .psigmaEta (ih1 H) (ih2 H) (ih3 H)
  | quotLiftMk _ _ _ _ _ _ ihA ihr ihB ihf ihh iha =>
    intro k Γ' H
    have h2 := ihr H
    have h4 := ihf H
    have h5 := ihh H
    rw [inst_relT] at h2
    rw [inst_arrow] at h4
    rw [inst_quotInvT] at h5
    exact .quotLiftMk (ihA H) h2 (ihB H) h4 h5 (iha H)

/-- **The substitution lemma.**  A derivation under a binder,
instantiated with a well-typed value for that binder. -/
theorem HasType.instantiate {Γ : List VExpr} {b B a A : VExpr}
    (hb : A :: Γ ⊢ b : B) (ha : Γ ⊢ a : A) : Γ ⊢ b.inst a : B.inst a :=
  ha.instN hb .zero

end Setlec.TT
