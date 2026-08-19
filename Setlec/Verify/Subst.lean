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
