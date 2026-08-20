import Setlec.Kernel.ExprOps
import Setlec.Verify.Shift

/-!
# Substituting a free variable by a term

`substFvarAt p a e` replaces every reachable `fvar p` leaf by `a` and
lowers higher `fvar` indices by one — the syntactic side of the
substitution lemma (`Setlec.Model.Subst`).  The key equation is the
*beta bridge*: opening a binder with a fresh variable and then
substituting that variable equals opening with the term directly.
-/

namespace Setlec.Expr

theorem looseBVarsBounded_mono {k k' : Nat} (h : k ≤ k') :
    ∀ {e : Expr}, looseBVarsBounded k e = true → looseBVarsBounded k' e = true := by
  intro e
  induction e generalizing k k' with
  | bvar i => simp_all [looseBVarsBounded]; omega
  | app f a ihf iha =>
    intro hb
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨ihf h hb.1, iha h hb.2⟩
  | lam n ty body m ihty ihbody =>
    intro hb
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨ihty h hb.1, ihbody (by omega) hb.2⟩
  | forallE n ty body m ihty ihbody =>
    intro hb
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨ihty h hb.1, ihbody (by omega) hb.2⟩
  | letE n ty val body ihty ihval ihbody =>
    intro hb
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨⟨ihty h hb.1.1, ihval h hb.1.2⟩, ihbody (by omega) hb.2⟩
  | proj s i e ih =>
    intro hb
    simp only [looseBVarsBounded] at hb ⊢
    exact ih h hb
  | _ => simp [looseBVarsBounded]

/-- Instantiation is a no-op on terms without matching loose bvars. -/
theorem instantiate1_eq_self {v : Expr} :
    ∀ {e : Expr} {k : Nat}, looseBVarsBounded k e = true → e.instantiate1 v k = e := by
  intro e
  induction e with
  | bvar i =>
    intro k hb
    simp only [looseBVarsBounded, decide_eq_true_eq] at hb
    have h1 : ¬ i = k := by omega
    have h2 : ¬ i > k := by omega
    simp [instantiate1, h1, h2]
  | _ =>
    intro k hb
    simp_all [looseBVarsBounded, instantiate1]

/-- Two closed instantiations commute (the outer index below the
inner). -/
theorem instantiate1_instantiate1 {a b : Expr}
    (hba : a.looseBVarsBounded 0 = true)
    (hbb : b.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (j k : Nat), j ≤ k →
      (e.instantiate1 a (k + 1)).instantiate1 b j =
        (e.instantiate1 b j).instantiate1 a k := by
  intro e
  induction e with
  | bvar i =>
    intro j k hjk
    repeat' first
      | (exact instantiate1_eq_self
          (looseBVarsBounded_mono (Nat.zero_le _) hba))
      | (exact instantiate1_eq_self
          (looseBVarsBounded_mono (Nat.zero_le _) hbb))
      | (exact (instantiate1_eq_self
          (looseBVarsBounded_mono (Nat.zero_le _) hba)).symm)
      | (exact (instantiate1_eq_self
          (looseBVarsBounded_mono (Nat.zero_le _) hbb)).symm)
      | rfl
      | (exact congrArg Expr.bvar (by omega))
      | (exact absurd rfl (by omega))
      | omega
      | simp only [instantiate1]
      | split
  | fvar idx n ty => intro j k hjk; simp [instantiate1]
  | sort u => intro j k hjk; simp [instantiate1]
  | const n us => intro j k hjk; simp [instantiate1]
  | app f g ihf ihg => intro j k hjk; simp [instantiate1, ihf _ _ hjk, ihg _ _ hjk]
  | lam n ty body m ihty ihbody =>
    intro j k hjk
    simp [instantiate1, ihty _ _ hjk, ihbody _ _ (by omega : j + 1 ≤ k + 1)]
  | forallE n ty body m ihty ihbody =>
    intro j k hjk
    simp [instantiate1, ihty _ _ hjk, ihbody _ _ (by omega : j + 1 ≤ k + 1)]
  | letE n ty v body ihty ihv ihbody =>
    intro j k hjk
    simp [instantiate1, ihty _ _ hjk, ihv _ _ hjk,
      ihbody _ _ (by omega : j + 1 ≤ k + 1)]
  | lit l => intro j k hjk; simp [instantiate1]
  | proj s i e ih => intro j k hjk; simp [instantiate1, ih _ _ hjk]

/-- Instantiation preserves a `∀`-telescope's arity. -/
theorem stripPis_instantiate1_isSome {v : Expr} :
    ∀ (k : Nat) {e : Expr} (j : Nat), (e.stripPis k).isSome →
      ((e.instantiate1 v j).stripPis k).isSome := by
  intro k
  induction k with
  | zero => intro e j _; simp [stripPis]
  | succ k ih =>
    intro e j h
    match e, h with
    | .forallE n ty body m, h =>
      simp only [instantiate1, stripPis, Option.isSome_map] at h ⊢
      exact ih (j + 1) h

/-- Structural equality up to `fvar` names and annotations and binder
names — exactly what the interpretation never reads. -/
def ErasedEq : Expr → Expr → Prop
  | .bvar i, .bvar j => i = j
  | .fvar i _ _, .fvar j _ _ => i = j
  | .sort u, .sort v => u = v
  | .const n us, .const n' us' => n = n' ∧ us = us'
  | .app f a, .app g b => ErasedEq f g ∧ ErasedEq a b
  | .lam _ ty b m, .lam _ ty' b' m' =>
    m = m' ∧ ErasedEq ty ty' ∧ ErasedEq b b'
  | .forallE _ ty b m, .forallE _ ty' b' m' =>
    m = m' ∧ ErasedEq ty ty' ∧ ErasedEq b b'
  | .letE _ ty v b, .letE _ ty' v' b' =>
    ErasedEq ty ty' ∧ ErasedEq v v' ∧ ErasedEq b b'
  | .lit l, .lit l' => l = l'
  | .proj s i e, .proj s' i' e' => s = s' ∧ i = i' ∧ ErasedEq e e'
  | _, _ => False

theorem ErasedEq.rfl : ∀ (e : Expr), ErasedEq e e := by
  intro e
  induction e <;> simp_all [ErasedEq]

theorem ErasedEq.instantiate1 :
    ∀ {e e' v v' : Expr} {k : Nat}, ErasedEq e e' → ErasedEq v v' →
      ErasedEq (e.instantiate1 v k) (e'.instantiate1 v' k) := by
  intro e
  induction e with
  | bvar i =>
    intro e' v v' k he hv
    match e', he with
    | .bvar j, he =>
      obtain rfl : i = j := he
      simp only [Expr.instantiate1]
      split
      · exact hv
      · split <;> simp [ErasedEq]
  | fvar idx n ty =>
    intro e' v v' k he hv
    match e', he with
    | .fvar j n' ty', he => simpa [Expr.instantiate1, ErasedEq] using he
  | sort u =>
    intro e' v v' k he hv
    match e', he with
    | .sort u', he => simpa [Expr.instantiate1, ErasedEq] using he
  | const n us =>
    intro e' v v' k he hv
    match e', he with
    | .const n' us', he => simpa [Expr.instantiate1, ErasedEq] using he
  | app f a ihf iha =>
    intro e' v v' k he hv
    match e', he with
    | .app g b, he =>
      exact ⟨ihf he.1 hv, iha he.2 hv⟩
  | lam n ty body m ihty ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .lam n' ty' body' m', he =>
      exact ⟨he.1, ihty he.2.1 hv, ihbody he.2.2 hv⟩
  | forallE n ty body m ihty ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .forallE n' ty' body' m', he =>
      exact ⟨he.1, ihty he.2.1 hv, ihbody he.2.2 hv⟩
  | letE n ty vl body ihty ihv ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .letE n' ty' vl' body', he =>
      exact ⟨ihty he.1 hv, ihv he.2.1 hv, ihbody he.2.2 hv⟩
  | lit l =>
    intro e' v v' k he hv
    match e', he with
    | .lit l', he => simpa [Expr.instantiate1, ErasedEq] using he
  | proj sn i pe ih =>
    intro e' v v' k he hv
    match e', he with
    | .proj sn' i' pe', he =>
      exact ⟨he.1, he.2.1, ih he.2.2 hv⟩

/-- The first `k` binder domains of a λ-tower and a `∀`-telescope agree
syntactically. -/
def LamPiDomsEq : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | k + 1, .lam _ d₁ b₁ _, .forallE _ d₂ b₂ _ => d₁ = d₂ ∧ LamPiDomsEq k b₁ b₂
  | _ + 1, _, _ => False

/-- Domain agreement survives instantiation (same argument on both
sides). -/
theorem LamPiDomsEq.instantiate1 {v : Expr} :
    ∀ (k : Nat) {e₁ e₂ : Expr} (j : Nat), LamPiDomsEq k e₁ e₂ →
      LamPiDomsEq k (e₁.instantiate1 v j) (e₂.instantiate1 v j) := by
  intro k
  induction k with
  | zero => intro e₁ e₂ j _; trivial
  | succ k ih =>
    intro e₁ e₂ j h
    match e₁, e₂, h with
    | .lam n₁ d₁ b₁ m₁, .forallE n₂ d₂ b₂ m₂, h =>
      exact ⟨by rw [h.1], ih (j + 1) h.2⟩

/-- Lifting a bvar-closed expression is the identity. -/
theorem liftLooseBVars_eq_self {k : Nat} :
    ∀ {e : Expr} {c : Nat}, e.looseBVarsBounded c = true →
      e.liftLooseBVars k c = e := by
  intro e
  induction e with
  | bvar i =>
    intro c hb
    simp only [looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [liftLooseBVars]
    rw [if_neg (by omega)]
  | _ =>
    intro c hb
    simp_all [looseBVarsBounded, liftLooseBVars]

/-- A zero lift is the identity. -/
theorem liftLooseBVars_zero : ∀ (e : Expr) (c : Nat),
    e.liftLooseBVars 0 c = e := by
  intro e
  induction e <;> intro c <;> simp_all [liftLooseBVars]

/-- Instantiating any freshly inserted slot of a lift eats one lift
level: the lifted expression never references the inserted range. -/
theorem instantiate1_liftLooseBVars {v : Expr} :
    ∀ {e : Expr} {k c j : Nat}, c ≤ j → j ≤ c + k →
      (e.liftLooseBVars (k + 1) c).instantiate1 v j =
        e.liftLooseBVars k c := by
  intro e
  induction e with
  | bvar i =>
    intro k c j hcj hjk
    simp only [liftLooseBVars]
    split
    · next h =>
      simp only [instantiate1]
      rw [if_neg (by omega), if_pos (by omega)]
      exact congrArg Expr.bvar (by omega)
    · next h =>
      simp only [instantiate1]
      rw [if_neg (by omega), if_neg (by omega)]
  | fvar idx n ty => intro k c j hcj hjk; rfl
  | sort u => intro k c j hcj hjk; rfl
  | const n us => intro k c j hcj hjk; rfl
  | app f a ihf iha =>
    intro k c j hcj hjk
    simp only [liftLooseBVars, instantiate1, ihf hcj hjk, iha hcj hjk]
  | lam n ty body m ihty ihbody =>
    intro k c j hcj hjk
    simp only [liftLooseBVars, instantiate1, ihty hcj hjk,
      ihbody (by omega : c + 1 ≤ j + 1) (by omega : j + 1 ≤ c + 1 + k)]
  | forallE n ty body m ihty ihbody =>
    intro k c j hcj hjk
    simp only [liftLooseBVars, instantiate1, ihty hcj hjk,
      ihbody (by omega : c + 1 ≤ j + 1) (by omega : j + 1 ≤ c + 1 + k)]
  | letE n ty vl body ihty ihv ihbody =>
    intro k c j hcj hjk
    simp only [liftLooseBVars, instantiate1, ihty hcj hjk, ihv hcj hjk,
      ihbody (by omega : c + 1 ≤ j + 1) (by omega : j + 1 ≤ c + 1 + k)]
  | lit l => intro k c j hcj hjk; rfl
  | proj sn i pe ih =>
    intro k c j hcj hjk
    simp only [liftLooseBVars, instantiate1, ih hcj hjk]

/-- Instantiation below the lift's cutoff commutes with the lift. -/
theorem liftLooseBVars_instantiate1 {v : Expr}
    (hbv : v.looseBVarsBounded 0 = true) :
    ∀ {e : Expr} {k c j : Nat}, j ≥ c →
      (e.liftLooseBVars k c).instantiate1 v (j + k) =
        (e.instantiate1 v j).liftLooseBVars k c := by
  intro e
  induction e with
  | bvar i =>
    intro k c j hjc
    simp only [liftLooseBVars]
    split
    · next h =>
      simp only [instantiate1]
      by_cases h1 : i = j
      · rw [if_pos (by omega : i + k = j + k), if_pos h1,
          liftLooseBVars_eq_self (looseBVarsBounded_mono (Nat.zero_le _) hbv)]
      · rw [if_neg (by omega : ¬ i + k = j + k), if_neg h1]
        by_cases h2 : i > j
        · rw [if_pos (by omega), if_pos h2]
          simp only [liftLooseBVars]
          rw [if_pos (by omega)]
          congr 1
          omega
        · rw [if_neg (by omega), if_neg h2]
          simp only [liftLooseBVars]
          rw [if_pos h]
    · next h =>
      simp only [instantiate1]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
      simp only [liftLooseBVars]
      rw [if_neg h]
  | fvar idx n ty => intro k c j hjc; rfl
  | sort u => intro k c j hjc; rfl
  | const n us => intro k c j hjc; rfl
  | app f a ihf iha =>
    intro k c j hjc
    simp only [liftLooseBVars, instantiate1, ihf hjc, iha hjc]
  | lam n ty body m ihty ihbody =>
    intro k c j hjc
    simp only [liftLooseBVars, instantiate1, ihty hjc]
    rw [show j + k + 1 = (j + 1) + k from by omega,
      ihbody (by omega : j + 1 ≥ c + 1)]
  | forallE n ty body m ihty ihbody =>
    intro k c j hjc
    simp only [liftLooseBVars, instantiate1, ihty hjc]
    rw [show j + k + 1 = (j + 1) + k from by omega,
      ihbody (by omega : j + 1 ≥ c + 1)]
  | letE n ty vl body ihty ihv ihbody =>
    intro k c j hjc
    simp only [liftLooseBVars, instantiate1, ihty hjc, ihv hjc]
    rw [show j + k + 1 = (j + 1) + k from by omega,
      ihbody (by omega : j + 1 ≥ c + 1)]
  | lit l => intro k c j hjc; rfl
  | proj sn i pe ih =>
    intro k c j hjc
    simp only [liftLooseBVars, instantiate1, ih hjc]

/-- Renaming constants moves no `fvar` indices. -/
theorem fvarsBelow_renameConsts {f : Name → Name} :
    ∀ {e : Expr} {d : Nat}, fvarsBelow d e → fvarsBelow d (e.renameConsts f) := by
  intro e
  induction e <;> intro d h <;> simp_all [fvarsBelow, renameConsts]

/-- Erasure-equal expressions have the same `fvar` indices. -/
theorem fvarsBelow_erasedEq :
    ∀ {e₁ e₂ : Expr} {d : Nat}, ErasedEq e₁ e₂ → fvarsBelow d e₁ →
      fvarsBelow d e₂ := by
  intro e₁
  induction e₁ with
  | bvar i => intro e₂ d he _; match e₂, he with
    | .bvar j, _ => trivial
  | fvar idx n ty => intro e₂ d he hb; match e₂, he with
    | .fvar j n' ty', he =>
      obtain rfl : idx = j := he
      exact hb
  | sort u => intro e₂ d he _; match e₂, he with
    | .sort u', _ => trivial
  | const n us => intro e₂ d he _; match e₂, he with
    | .const n' us', _ => trivial
  | app f a ihf iha => intro e₂ d he hb; match e₂, he with
    | .app g b, he => exact ⟨ihf he.1 hb.1, iha he.2 hb.2⟩
  | lam n ty body m ihty ihbody => intro e₂ d he hb; match e₂, he with
    | .lam n' ty' body' m', he =>
      exact ⟨ihty he.2.1 hb.1, ihbody he.2.2 hb.2⟩
  | forallE n ty body m ihty ihbody => intro e₂ d he hb; match e₂, he with
    | .forallE n' ty' body' m', he =>
      exact ⟨ihty he.2.1 hb.1, ihbody he.2.2 hb.2⟩
  | letE n ty vl body ihty ihv ihbody => intro e₂ d he hb; match e₂, he with
    | .letE n' ty' vl' body', he =>
      exact ⟨ihty he.1 hb.1, ihv he.2.1 hb.2.1, ihbody he.2.2 hb.2.2⟩
  | lit l => intro e₂ d he _; match e₂, he with
    | .lit l', _ => trivial
  | proj sn i pe ih => intro e₂ d he hb; match e₂, he with
    | .proj sn' i' pe', he =>
      show fvarsBelow d pe'
      exact ih he.2.2 hb

/-- Instantiation distributes over a `∀`-telescope's decomposition:
each domain is instantiated at its depth-shifted index, the body at
the telescope's arity. -/
theorem stripPis_instantiate1_eq {v : Expr} :
    ∀ (k : Nat) {e : Expr} {bs bs' : List (Name × Expr × BinderMeta)}
      {body body' : Expr} (j : Nat),
      e.stripPis k = some (bs, body) →
      (e.instantiate1 v j).stripPis k = some (bs', body') →
      body' = body.instantiate1 v (j + k) ∧
      ∀ (i : Nat) (b b' : Name × Expr × BinderMeta),
        bs[i]? = some b → bs'[i]? = some b' →
        b'.2.1 = b.2.1.instantiate1 v (j + i) := by
  intro k
  induction k with
  | zero =>
    intro e bs bs' body body' j h1 h2
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨rfl, fun i b b' hb _ => by simp at hb⟩
  | succ k ih =>
    intro e bs bs' body body' j h1 h2
    match e, h1 with
    | .forallE n d b m, h1 =>
      simp only [instantiate1, stripPis] at h1 h2
      cases hs1 : b.stripPis k with
      | none => rw [hs1] at h1; exact nomatch h1
      | some p1 =>
      cases hs2 : (b.instantiate1 v (j + 1)).stripPis k with
      | none => rw [hs2] at h2; exact nomatch h2
      | some p2 =>
      rw [hs1] at h1
      rw [hs2] at h2
      simp only [Option.map_some, Option.some.injEq] at h1 h2
      obtain ⟨hb1, hbody1⟩ : (n, d, m) :: p1.1 = bs ∧ p1.2 = body := by
        cases h1; exact ⟨rfl, rfl⟩
      obtain ⟨hb2, hbody2⟩ :
          (n, d.instantiate1 v j, m) :: p2.1 = bs' ∧ p2.2 = body' := by
        cases h2; exact ⟨rfl, rfl⟩
      subst hb1 hbody1 hb2 hbody2
      obtain ⟨hbody, hdoms⟩ := ih (j + 1) hs1 hs2
      refine ⟨by rw [hbody]; congr 1; omega, ?_⟩
      intro i bb bb' hbb hbb'
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hbb hbb'
        subst hbb hbb'
        simp
      | succ i =>
        simp only [List.getElem?_cons_succ] at hbb hbb'
        rw [hdoms i bb bb' hbb hbb']
        congr 1
        omega

/-- Instantiation distributes over an application spine. -/
theorem mkAppN_instantiate1 {v : Expr} :
    ∀ (args : List Expr) (h : Expr) (k : Nat),
      (Expr.mkAppN h args).instantiate1 v k =
        Expr.mkAppN (h.instantiate1 v k) (args.map (·.instantiate1 v k)) := by
  intro args
  induction args with
  | nil => intro h k; rfl
  | cons a args ih =>
    intro h k
    show (Expr.mkAppN (.app h a) args).instantiate1 v k = _
    rw [ih]
    rfl

/-- Erasure-equality is transitive. -/
theorem ErasedEq.trans :
    ∀ {e₁ e₂ e₃ : Expr}, ErasedEq e₁ e₂ → ErasedEq e₂ e₃ → ErasedEq e₁ e₃ := by
  intro e₁
  induction e₁ with
  | bvar i =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .bvar j, h12 =>
      match e₃, h23 with
      | .bvar l, h23 =>
        have a : i = j := h12
        have b : j = l := h23
        show i = l
        omega
  | fvar idx n ty =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .fvar j n₂ ty₂, h12 =>
      match e₃, h23 with
      | .fvar l n₃ ty₃, h23 =>
        have a : idx = j := h12
        have b : j = l := h23
        show idx = l
        omega
  | sort u =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .sort u₂, h12 =>
      match e₃, h23 with
      | .sort u₃, h23 =>
        have a : u = u₂ := h12
        have b : u₂ = u₃ := h23
        show u = u₃
        exact a.trans b
  | const n us =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .const n₂ us₂, h12 =>
      match e₃, h23 with
      | .const n₃ us₃, h23 =>
        have a : n = n₂ ∧ us = us₂ := h12
        have b : n₂ = n₃ ∧ us₂ = us₃ := h23
        exact show n = n₃ ∧ us = us₃ from
          ⟨a.1.trans b.1, a.2.trans b.2⟩
  | app fe a ihf iha =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .app g b, h12 =>
      match e₃, h23 with
      | .app h c, h23 =>
        have x : ErasedEq fe g ∧ ErasedEq a b := h12
        have y : ErasedEq g h ∧ ErasedEq b c := h23
        exact show ErasedEq fe h ∧ ErasedEq a c from
          ⟨ihf x.1 y.1, iha x.2 y.2⟩
  | lam n ty body m ihty ihbody =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .lam n₂ ty₂ body₂ m₂, h12 =>
      match e₃, h23 with
      | .lam n₃ ty₃ body₃ m₃, h23 =>
        have x : m = m₂ ∧ ErasedEq ty ty₂ ∧ ErasedEq body body₂ := h12
        have y : m₂ = m₃ ∧ ErasedEq ty₂ ty₃ ∧ ErasedEq body₂ body₃ := h23
        exact show m = m₃ ∧ ErasedEq ty ty₃ ∧ ErasedEq body body₃ from
          ⟨x.1.trans y.1, ihty x.2.1 y.2.1, ihbody x.2.2 y.2.2⟩
  | forallE n ty body m ihty ihbody =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .forallE n₂ ty₂ body₂ m₂, h12 =>
      match e₃, h23 with
      | .forallE n₃ ty₃ body₃ m₃, h23 =>
        have x : m = m₂ ∧ ErasedEq ty ty₂ ∧ ErasedEq body body₂ := h12
        have y : m₂ = m₃ ∧ ErasedEq ty₂ ty₃ ∧ ErasedEq body₂ body₃ := h23
        exact show m = m₃ ∧ ErasedEq ty ty₃ ∧ ErasedEq body body₃ from
          ⟨x.1.trans y.1, ihty x.2.1 y.2.1, ihbody x.2.2 y.2.2⟩
  | letE n ty vl body ihty ihv ihbody =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .letE n₂ ty₂ vl₂ body₂, h12 =>
      match e₃, h23 with
      | .letE n₃ ty₃ vl₃ body₃, h23 =>
        have x : ErasedEq ty ty₂ ∧ ErasedEq vl vl₂ ∧ ErasedEq body body₂ :=
          h12
        have y : ErasedEq ty₂ ty₃ ∧ ErasedEq vl₂ vl₃ ∧
            ErasedEq body₂ body₃ := h23
        exact show ErasedEq ty ty₃ ∧ ErasedEq vl vl₃ ∧
            ErasedEq body body₃ from
          ⟨ihty x.1 y.1, ihv x.2.1 y.2.1, ihbody x.2.2 y.2.2⟩
  | lit l =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .lit l₂, h12 =>
      match e₃, h23 with
      | .lit l₃, h23 =>
        have a : l = l₂ := h12
        have b : l₂ = l₃ := h23
        show l = l₃
        exact a.trans b
  | proj sn i pe ih =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .proj sn₂ i₂ pe₂, h12 =>
      match e₃, h23 with
      | .proj sn₃ i₃ pe₃, h23 =>
        have x : sn = sn₂ ∧ i = i₂ ∧ ErasedEq pe pe₂ := h12
        have y : sn₂ = sn₃ ∧ i₂ = i₃ ∧ ErasedEq pe₂ pe₃ := h23
        exact show sn = sn₃ ∧ i = i₃ ∧ ErasedEq pe pe₃ from
          ⟨x.1.trans y.1, x.2.1.trans y.2.1, ih x.2.2 y.2.2⟩

/-- Instantiate a sequence of arguments at descending indices (the
per-domain effect of peeling a telescope). -/
def instSeq : List Expr → Nat → Expr → Expr
  | [], _, e => e
  | a :: as, t, e => instSeq as (t - 1) (e.instantiate1 a t)

/-- `instSeq` congruence under erasure (arguments erased to
themselves). -/
theorem instSeq_erasedEq :
    ∀ (args : List Expr) (t : Nat) {X Y : Expr}, ErasedEq X Y →
      ErasedEq (instSeq args t X) (instSeq args t Y) := by
  intro args
  induction args with
  | nil => intro t X Y h; exact h
  | cons a as ih =>
    intro t X Y h
    exact ih (t - 1) (ErasedEq.instantiate1 h (ErasedEq.rfl a))

/-- Instantiations strictly above a lift's inserted range drop past
it. -/
theorem instSeq_liftLooseBVars {kL c : Nat} :
    ∀ (args : List Expr) (t : Nat) {e : Expr},
      (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      t + 1 ≥ args.length + c + kL →
      instSeq args t (e.liftLooseBVars kL c) =
        (instSeq args (t - kL) e).liftLooseBVars kL c := by
  intro args
  induction args with
  | nil => intro t e _ _; rfl
  | cons a as ih =>
    intro t e hb ht
    simp only [List.length_cons] at ht
    obtain ⟨j, rfl⟩ : ∃ j, t = j + kL := ⟨t - kL, by omega⟩
    show instSeq as (j + kL - 1)
        ((e.liftLooseBVars kL c).instantiate1 a (j + kL)) =
      (instSeq as (j + kL - kL - 1)
        (e.instantiate1 a (j + kL - kL))).liftLooseBVars kL c
    rw [liftLooseBVars_instantiate1 (hb a List.mem_cons_self)
      (by omega : j ≥ c)]
    rw [show j + kL - kL = j from by omega]
    rw [ih (j + kL - 1) (fun x hx => hb x (List.mem_cons_of_mem _ hx))
      (by omega)]
    rw [show j + kL - 1 - kL = j - 1 from by omega]

/-- Instantiating every inserted slot of a lift, top down, restores the
original expression. -/
theorem instSeq_lift_eat {c : Nat} :
    ∀ (extras : List Expr) {e : Expr},
      instSeq extras (c + extras.length - 1)
        (e.liftLooseBVars extras.length c) = e := by
  intro extras
  induction extras with
  | nil => intro e; exact liftLooseBVars_zero e c
  | cons x xs ih =>
    intro e
    show instSeq xs (c + (xs.length + 1) - 1 - 1)
      ((e.liftLooseBVars (xs.length + 1) c).instantiate1 x
        (c + (xs.length + 1) - 1)) = e
    rw [instantiate1_liftLooseBVars (by omega) (by omega)]
    rw [show c + (xs.length + 1) - 1 - 1 = c + xs.length - 1 from by omega]
    exact ih

/-- A successful telescope decomposition has exactly `k` binders. -/
theorem stripPis_length :
    ∀ (k : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr}, e.stripPis k = some (bs, body) → bs.length = k := by
  intro k
  induction k with
  | zero =>
    intro e bs body h
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ k ih =>
    intro e bs body h
    match e, h with
    | .forallE n d b m, h =>
      simp only [stripPis] at h
      cases hs : b.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hb, -⟩ : (n, d, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hb
        have := ih (e := b) (bs := p.1) (body := p.2) (by rw [hs])
        simp [this]

/-- An instantiation sequence splits along list append. -/
theorem instSeq_append :
    ∀ (as bs : List Expr) (t : Nat) (X : Expr),
      instSeq (as ++ bs) t X = instSeq bs (t - as.length) (instSeq as t X) := by
  intro as
  induction as with
  | nil => intro bs t X; simp [instSeq]
  | cons a as ih =>
    intro bs t X
    show instSeq (as ++ bs) (t - 1) (X.instantiate1 a t) = _
    rw [ih bs (t - 1) (X.instantiate1 a t)]
    congr 1
    simp
    omega

/-- An instantiation sequence is a no-op on bvar-closed expressions. -/
theorem instSeq_eq_self :
    ∀ (args : List Expr) (t : Nat) {e : Expr},
      e.looseBVarsBounded 0 = true → instSeq args t e = e := by
  intro args
  induction args with
  | nil => intro t e _; rfl
  | cons a as ih =>
    intro t e hb
    show instSeq as (t - 1) (e.instantiate1 a t) = e
    rw [instantiate1_eq_self (looseBVarsBounded_mono (Nat.zero_le t) hb)]
    exact ih (t - 1) hb

/-- An instantiation sequence distributes over an application spine. -/
theorem instSeq_mkAppN :
    ∀ (args : List Expr) (t : Nat) (h : Expr) (xs : List Expr),
      instSeq args t (Expr.mkAppN h xs) =
        Expr.mkAppN (instSeq args t h) (xs.map (instSeq args t ·)) := by
  intro args
  induction args with
  | nil => intro t h xs; simp [instSeq]
  | cons a as ih =>
    intro t h xs
    show instSeq as (t - 1) ((Expr.mkAppN h xs).instantiate1 a t) = _
    rw [mkAppN_instantiate1, ih]
    congr 1
    simp only [List.map_map]
    rfl

/-- Resolving a bound variable through an instantiation sequence of
closed arguments: the variable becomes its slot's argument. -/
theorem instSeq_bvar :
    ∀ (args : List Expr) (t j : Nat),
      (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      j ≤ t → t - j < args.length →
      args[t - j]? = some (instSeq args t (.bvar j)) := by
  intro args
  induction args with
  | nil => intro t j _ _ h; simp at h
  | cons a as ih =>
    intro t j hb hj hr
    by_cases hjt : j = t
    · subst hjt
      show (a :: as)[j - j]? = some (instSeq as (j - 1)
        ((Expr.bvar j).instantiate1 a j))
      simp only [Expr.instantiate1, ↓reduceIte]
      rw [instSeq_eq_self as (j - 1) (hb a List.mem_cons_self)]
      simp [Nat.sub_self]
    · have hjlt : j < t := by omega
      show (a :: as)[t - j]? = some (instSeq as (t - 1)
        ((Expr.bvar j).instantiate1 a t))
      simp only [Expr.instantiate1]
      rw [if_neg hjt, if_neg (by omega)]
      rw [show t - j = (t - 1 - j) + 1 from by omega]
      rw [List.getElem?_cons_succ]
      exact ih (t - 1) j (fun x hx => hb x (List.mem_cons_of_mem _ hx))
        (by omega) (by simp at hr; omega)

/-- A successful λ-tower decomposition has exactly `k` binders. -/
theorem stripLams_length :
    ∀ (k : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr}, e.stripLams k = some (bs, body) → bs.length = k := by
  intro k
  induction k with
  | zero =>
    intro e bs body h
    simp only [stripLams, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ k ih =>
    intro e bs body h
    match e, h with
    | .lam n d b m, h =>
      simp only [stripLams] at h
      cases hs : b.stripLams k with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hb, -⟩ : (n, d, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hb
        have := ih (e := b) (bs := p.1) (body := p.2) (by rw [hs])
        simp [this]

/-- Instantiation preserves a λ-tower's arity. -/
theorem stripLams_instantiate1_isSome {v : Expr} :
    ∀ (k : Nat) {e : Expr} (j : Nat), (e.stripLams k).isSome →
      ((e.instantiate1 v j).stripLams k).isSome := by
  intro k
  induction k with
  | zero => intro e j _; simp [stripLams]
  | succ k ih =>
    intro e j h
    match e, h with
    | .lam n ty body m, h =>
      simp only [instantiate1, stripLams, Option.isSome_map] at h ⊢
      exact ih (j + 1) h

/-- Instantiation distributes over a λ-tower's decomposition. -/
theorem stripLams_instantiate1_eq {v : Expr} :
    ∀ (k : Nat) {e : Expr} {bs bs' : List (Name × Expr × BinderMeta)}
      {body body' : Expr} (j : Nat),
      e.stripLams k = some (bs, body) →
      (e.instantiate1 v j).stripLams k = some (bs', body') →
      body' = body.instantiate1 v (j + k) ∧
      ∀ (i : Nat) (b b' : Name × Expr × BinderMeta),
        bs[i]? = some b → bs'[i]? = some b' →
        b'.2.1 = b.2.1.instantiate1 v (j + i) := by
  intro k
  induction k with
  | zero =>
    intro e bs bs' body body' j h1 h2
    simp only [stripLams, Option.some.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨rfl, fun i b b' hb _ => by simp at hb⟩
  | succ k ih =>
    intro e bs bs' body body' j h1 h2
    match e, h1 with
    | .lam n d b m, h1 =>
      simp only [instantiate1, stripLams] at h1 h2
      cases hs1 : b.stripLams k with
      | none => rw [hs1] at h1; exact nomatch h1
      | some p1 =>
      cases hs2 : (b.instantiate1 v (j + 1)).stripLams k with
      | none => rw [hs2] at h2; exact nomatch h2
      | some p2 =>
      rw [hs1] at h1
      rw [hs2] at h2
      simp only [Option.map_some, Option.some.injEq] at h1 h2
      obtain ⟨hb1, hbody1⟩ : (n, d, m) :: p1.1 = bs ∧ p1.2 = body := by
        cases h1; exact ⟨rfl, rfl⟩
      obtain ⟨hb2, hbody2⟩ :
          (n, d.instantiate1 v j, m) :: p2.1 = bs' ∧ p2.2 = body' := by
        cases h2; exact ⟨rfl, rfl⟩
      subst hb1 hbody1 hb2 hbody2
      obtain ⟨hbody, hdoms⟩ := ih (j + 1) hs1 hs2
      refine ⟨by rw [hbody]; congr 1; omega, ?_⟩
      intro i bb bb' hbb hbb'
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hbb hbb'
        subst hbb hbb'
        simp
      | succ i =>
        simp only [List.getElem?_cons_succ] at hbb hbb'
        rw [hdoms i bb bb' hbb hbb']
        congr 1
        omega

/-- A longer telescope decomposition restricts to a shorter one with
the binder-list prefix. -/
theorem stripPis_prefix :
    ∀ (a b : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr},
      e.stripPis (a + b) = some (bs, body) →
      ∃ body', e.stripPis a = some (bs.take a, body') := by
  intro a
  induction a with
  | zero => intro b e bs body h; exact ⟨e, by simp [stripPis]⟩
  | succ a ih =>
    intro b e bs body h
    rw [show a + 1 + b = (a + b) + 1 from by omega] at h
    match e, h with
    | .forallE n d bo m, h =>
      simp only [stripPis] at h ⊢
      cases hs : bo.stripPis (a + b) with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hb, -⟩ : (n, d, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        obtain ⟨body', hbody'⟩ := ih b (bs := p.1) (body := p.2) (by rw [hs])
        refine ⟨body', ?_⟩
        rw [hbody']
        subst hb
        simp

/-- Instantiating with a bounded term keeps loose-bvar bounds. -/
theorem looseBVarsBounded_instantiate1_gen {a : Expr}
    (hba : a.looseBVarsBounded 0 = true) :
    ∀ {e : Expr} {k : Nat}, looseBVarsBounded (k + 1) e = true →
      looseBVarsBounded k (e.instantiate1 a k) = true := by
  intro e
  induction e with
  | bvar i =>
    intro k hb
    simp only [looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [instantiate1]
    split
    · exact looseBVarsBounded_mono (Nat.zero_le k) hba
    · split <;> simp [looseBVarsBounded] <;> omega
  | _ =>
    intro k hb
    simp_all [looseBVarsBounded, instantiate1]

/-- Instantiating with a scoped term keeps reachable-`fvar` bounds. -/
theorem fvarsBelow_instantiate1_gen {d : Nat} {a : Expr} (ha : fvarsBelow d a) :
    ∀ {e : Expr} (k : Nat), fvarsBelow d e → fvarsBelow d (e.instantiate1 a k) := by
  intro e
  induction e <;> intro k hb <;> simp_all [instantiate1, fvarsBelow]
  case bvar i =>
    split
    · exact ha
    · split <;> simp [fvarsBelow]

/-- Replace `fvar p` by `a`, lowering higher `fvar` indices. -/
def substFvarAt (p : Nat) (a : Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx n ty =>
    if idx = p then a
    else if idx > p then .fvar (idx - 1) n (substFvarAt p a ty)
    else .fvar idx n ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f b => .app (substFvarAt p a f) (substFvarAt p a b)
  | .lam n ty body m => .lam n (substFvarAt p a ty) (substFvarAt p a body) m
  | .forallE n ty body m => .forallE n (substFvarAt p a ty) (substFvarAt p a body) m
  | .letE n ty val body =>
    .letE n (substFvarAt p a ty) (substFvarAt p a val) (substFvarAt p a body)
  | .lit l => .lit l
  | .proj s i e => .proj s i (substFvarAt p a e)

theorem substFvarAt_eq_self {p : Nat} {a : Expr} :
    ∀ {e : Expr}, fvarsBelow p e → substFvarAt p a e = e := by
  intro e
  induction e with
  | fvar idx n ty ih =>
    intro hb
    simp only [fvarsBelow] at hb
    have h1 : ¬ idx = p := by omega
    have h2 : ¬ idx > p := by omega
    simp [substFvarAt, h1, h2]
  | _ =>
    intro hb
    simp_all [fvarsBelow, substFvarAt]

/-- Substitution commutes with opening a binder at a higher index. -/
theorem substFvarAt_instantiate1 {p d : Nat} (hpd : p ≤ d) {n : Name} {ty a : Expr}
    (hba : a.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k : Nat),
      substFvarAt p a (e.instantiate1 (.fvar (d + 1) n ty) k) =
        (substFvarAt p a e).instantiate1 (.fvar d n (substFvarAt p a ty)) k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [instantiate1, substFvarAt]
    split
    · have h1 : ¬ (d + 1 = p) := by omega
      have h2 : d + 1 > p := by omega
      simp [substFvarAt, h1, h2]
    · split <;> simp [substFvarAt]
  | fvar idx n' ty' ih =>
    intro k
    simp only [instantiate1, substFvarAt]
    by_cases h1 : idx = p
    · simp only [h1, if_true]
      exact (instantiate1_eq_self (looseBVarsBounded_mono (Nat.zero_le k) hba)).symm
    · by_cases h2 : idx > p
      · simp [h1, h2, instantiate1]
      · simp [h1, h2, instantiate1]
  | _ =>
    intro k
    simp_all [instantiate1, substFvarAt]

/-- The beta bridge: opening with a fresh variable, then substituting it,
equals opening with the term directly. -/
theorem substFvarAt_instantiate1_self {d : Nat} {n : Name} {ty a : Expr} :
    ∀ (e : Expr) (k : Nat), fvarsBelow d e →
      substFvarAt d a (e.instantiate1 (.fvar d n ty) k) = e.instantiate1 a k := by
  intro e
  induction e with
  | bvar i =>
    intro k hb
    simp only [instantiate1]
    split
    · simp [substFvarAt]
    · split <;> simp [substFvarAt]
  | fvar idx n' ty' ih =>
    intro k hb
    simp only [fvarsBelow] at hb
    have h1 : ¬ idx = d := by omega
    have h2 : ¬ idx > d := by omega
    simp [instantiate1, substFvarAt, h1, h2]
  | _ =>
    intro k hb
    simp_all [instantiate1, substFvarAt, fvarsBelow]

end Setlec.Expr
