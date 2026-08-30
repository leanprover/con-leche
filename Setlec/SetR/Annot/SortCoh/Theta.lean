import Setlec.SetR.Annot.SortCoh.LoopLock

/-!
# Run-level sort coherence — the Θ walk statement and the commutation kit

Split from `SortCoh.lean` (pure motion; the umbrella
`Setlec.SetR.Annot.SortCoh` re-exports the whole family).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec (CheckMode Env Expr Name Level inferTypeCore whnf whnfCore
  isDefEqCore unfoldDefinition)

section Discharge
variable {μ : CheckMode} {env : Env}

/-! ### The Θ walk (the summit statement, frozen per the treatment) -/

/-- One opened binder of the Θ telescope: the two binder names, the
ANNOTATION PAIR (each side opened with its own domain — the kernel's
`.fvar d nᵢ tyᵢ` discipline), and the ARGUMENT PAIR the subject
loops β-substituted where the run opened an fvar. -/
structure ThetaEntry where
  n₁ : Name
  n₂ : Name
  ty₁ : Expr
  ty₂ : Expr
  a₁ : Expr
  a₂ : Expr

/-- Left-side telescope substitution: close each opened fvar
(innermost first — the tail is deeper) and plug the loop's actual
argument. -/
def thetaSubst₁ : Nat → List ThetaEntry → Expr → Expr
  | _, [], e => e
  | d, t :: Γ, e =>
    ((thetaSubst₁ (d + 1) Γ e).abstract1 d).instantiate1 t.a₁

/-- Right-side telescope substitution. -/
def thetaSubst₂ : Nat → List ThetaEntry → Expr → Expr
  | _, [], e => e
  | d, t :: Γ, e =>
    ((thetaSubst₂ (d + 1) Γ e).abstract1 d).instantiate1 t.a₂

/-- The telescope's per-entry facts, entry `j` at depth `d + j`:
the argument zip, the domain fact (the run's own `hd` at the
entry's depth — the knot's defeq is `isDefEqCore` one fuel up),
and the arguments' subject packages. -/
def TelescopeOk (μ : CheckMode) (env : Env) (fcK : Nat) :
    Nat → List ThetaEntry → Prop
  | _, [] => True
  | d, t :: Γ =>
    CertZip μ env (fcK + 1) d t.a₁ t.a₂ ∧
    isDefEqCore μ env (fcK + 1) d t.ty₁ t.ty₂ = .ok true ∧
    SubjInv d t.a₁ ∧ SubjInv d t.a₂ ∧
    PairedLeaves t.a₁ t.a₂ ∧
    TelescopeOk μ env fcK (d + 1) Γ

/-- **The Θ walk's claim** (the summit): a pair of spines over
telescope-substituted, run-related cores, both loops reaching
sorts, agrees on the sort numerals.  At telescope depth zero with
`fcK := fc − 1`, `L := defeqLoopFuel` this is `ZipCertSpineCase`'s
data via `isDefEqCore`'s unfold; the four docket conversions are
its other consumers.  The walk's own recursion is the `[fcK, L]`
lex (pushes descend the knot; re-entries descend the budget); the
bar is for the rebased-pair conversions' zip-tier work. -/
def ThetaWalkClaim (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ (fcK L : Nat) {d ga la gb lb : Nat} {Γ : List ThetaEntry}
    {C₁ C₂ : Expr} {sp₁ sp₂ : List Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q (fcK + 1) (ga + gb) (la + lb) →
    TelescopeOk μ env fcK d Γ →
    Setlec.defeqLoop μ (Setlec.pureFns μ env fcK) env
      (d + Γ.length) L C₁ C₂ = .ok true →
    sp₁.length = sp₂.length →
    (∀ i (h₁ : i < sp₁.length) (h₂ : i < sp₂.length),
      CertZip μ env (fcK + 1) d sp₁[i] sp₂[i]) →
    SubjInv d (Setlec.Expr.mkAppN (thetaSubst₁ d Γ C₁) sp₁) →
    SubjInv d (Setlec.Expr.mkAppN (thetaSubst₂ d Γ C₂) sp₂) →
    PairedLeaves (Setlec.Expr.mkAppN (thetaSubst₁ d Γ C₁) sp₁)
      (Setlec.Expr.mkAppN (thetaSubst₂ d Γ C₂) sp₂) →
    Q d (Setlec.Expr.mkAppN (thetaSubst₁ d Γ C₁) sp₁)
      (Setlec.Expr.mkAppN (thetaSubst₂ d Γ C₂) sp₂) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN (thetaSubst₁ d Γ C₁) sp₁)
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN (thetaSubst₂ d Γ C₂) sp₂)
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **The θ-zip walk claim** (the audited architecture's second
summit phase, map-sealed after the θ-image-of-cert wall ruling):
spines over telescope-images of a ZIPPED pair — the walk proper is
its cert-arm's run-form; the syn/congruence material enters through
refl/`fcz`-lowered zips.  The audited measure (proof-internal):
`[rank, |Γ|, phase, zip-structure/L, budgets]` with `rank :=
max fcz (fcK+1)`-flavored bookkeeping recorded in DESIGN — the
in-zone-fvar recursion drops `|Γ|` at equal rank; the cert-arm
drops phase at equal rank; pushes drop the rank. -/
def ThetaZipWalkClaim (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ (fcz fcK : Nat) {d ga la gb lb : Nat} {Γ : List ThetaEntry}
    {A₁ A₂ : Expr} {sp₁ sp₂ : List Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q (fcK + 1) (ga + gb) (la + lb) →
    fcz ≤ fcK + 1 →
    TelescopeOk μ env fcK d Γ →
    CertZip μ env fcz (d + Γ.length) A₁ A₂ →
    sp₁.length = sp₂.length →
    (∀ i (h₁ : i < sp₁.length) (h₂ : i < sp₂.length),
      CertZip μ env (fcK + 1) d sp₁[i] sp₂[i]) →
    SubjInv d (Setlec.Expr.mkAppN (thetaSubst₁ d Γ A₁) sp₁) →
    SubjInv d (Setlec.Expr.mkAppN (thetaSubst₂ d Γ A₂) sp₂) →
    PairedLeaves (Setlec.Expr.mkAppN (thetaSubst₁ d Γ A₁) sp₁)
      (Setlec.Expr.mkAppN (thetaSubst₂ d Γ A₂) sp₂) →
    Q d (Setlec.Expr.mkAppN (thetaSubst₁ d Γ A₁) sp₁)
      (Setlec.Expr.mkAppN (thetaSubst₂ d Γ A₂) sp₂) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN (thetaSubst₁ d Γ A₁) sp₁)
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN (thetaSubst₂ d Γ A₂) sp₂)
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-! ### The commutation kit (the subst-sim's per-step algebra) -/

/-- The telescope's one-binder substitution at cursor `k`: close
the opened fvar `d` to `bvar k`, then plug the argument there. -/
def substAK (d k : Nat) (a e : Expr) : Expr :=
  (e.abstract1 d k).instantiate1 a k

/-- `abstract1` is the identity on `d`-fresh terms (supplied by
`fvarLeaves_lt_of_wscoped` at the telescope's depths). -/
theorem abstract1_eq_self :
    ∀ {e : Expr} {d k : Nat},
      (∀ l ∈ e.fvarLeaves, l.1 ≠ d) → e.abstract1 d k = e := by
  intro e
  induction e with
  | bvar i => intro d k h; rfl
  | fvar idx n ty ih =>
    intro d k h
    have hne : idx ≠ d := h (idx, n, ty)
      (by simp [Setlec.Expr.fvarLeaves])
    simp [Setlec.Expr.abstract1, hne]
  | sort u => intro d k h; rfl
  | const n us => intro d k h; rfl
  | lit l => intro d k h; rfl
  | app f x ihf ihx =>
    intro d k h
    simp only [Setlec.Expr.abstract1]
    rw [ihf (fun l hl => h l (by
        simp only [Setlec.Expr.fvarLeaves]
        exact List.mem_append.2 (.inl hl))),
      ihx (fun l hl => h l (by
        simp only [Setlec.Expr.fvarLeaves]
        exact List.mem_append.2 (.inr hl)))]
  | lam n ty b m ihty ihb =>
    intro d k h
    simp only [Setlec.Expr.abstract1]
    rw [ihty (fun l hl => h l (by
        simp only [Setlec.Expr.fvarLeaves]
        exact List.mem_append.2 (.inl hl))),
      ihb (fun l hl => h l (by
        simp only [Setlec.Expr.fvarLeaves]
        exact List.mem_append.2 (.inr hl)))]
  | forallE n ty b m ihty ihb =>
    intro d k h
    simp only [Setlec.Expr.abstract1]
    rw [ihty (fun l hl => h l (by
        simp only [Setlec.Expr.fvarLeaves]
        exact List.mem_append.2 (.inl hl))),
      ihb (fun l hl => h l (by
        simp only [Setlec.Expr.fvarLeaves]
        exact List.mem_append.2 (.inr hl)))]
  | letE n ty v b ihty ihv ihb =>
    intro d k h
    simp only [Setlec.Expr.abstract1]
    rw [ihty (fun l hl => h l (by
        simp only [Setlec.Expr.fvarLeaves]
        exact List.mem_append.2 (.inl (List.mem_append.2
          (.inl hl))))),
      ihv (fun l hl => h l (by
        simp only [Setlec.Expr.fvarLeaves]
        exact List.mem_append.2 (.inl (List.mem_append.2
          (.inr hl))))),
      ihb (fun l hl => h l (by
        simp only [Setlec.Expr.fvarLeaves]
        exact List.mem_append.2 (.inr hl)))]
  | proj sn i e ih =>
    intro d k h
    simp only [Setlec.Expr.abstract1]
    rw [ih (fun l hl => h l (by
      simpa [Setlec.Expr.fvarLeaves] using hl))]

/-- The substitution collapses on `d`-fresh, cursor-bounded terms
(the spine arguments are `substAK`-INVARIANT — the substitution
acts only on the cores). -/
theorem substAK_eq_self {d k : Nat} {a e : Expr}
    (hfresh : ∀ l ∈ e.fvarLeaves, l.1 ≠ d)
    (hb : e.looseBVarsBounded k = true) :
    substAK d k a e = e := by
  unfold substAK
  rw [abstract1_eq_self hfresh]
  exact Setlec.Expr.instantiate1_eq_self hb

/-- Abstraction commutes with instantiation by a `d`-fresh, closed
argument (the cursor-shift form; the β/ζ composite's core). -/
theorem abstract1_instantiate1_comm {d : Nat} {X : Expr}
    (hXf : ∀ l ∈ X.fvarLeaves, l.1 ≠ d) :
    ∀ (e : Expr) (k : Nat),
      (e.abstract1 d (k + 1)).instantiate1 X k
        = (e.instantiate1 X k).abstract1 d k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [Setlec.Expr.abstract1, Setlec.Expr.instantiate1]
    by_cases h1 : i = k
    · rw [if_pos h1]
      exact (abstract1_eq_self hXf).symm
    · rw [if_neg h1]
      by_cases h2 : i > k
      · rw [if_pos h2]; rfl
      · rw [if_neg h2]; rfl
  | fvar idx n ty ih =>
    intro k
    simp only [Setlec.Expr.abstract1, Setlec.Expr.instantiate1]
    by_cases h1 : idx = d
    · rw [if_pos h1]
      simp only [Setlec.Expr.instantiate1]
      rw [if_neg (by omega : ¬ (k + 1 = k)),
        if_pos (by omega : k + 1 > k)]
      simp [h1]
    · rw [if_neg h1]
      simp only [Setlec.Expr.instantiate1]
      rw [if_neg h1]
  | sort u => intro k; rfl
  | const n us => intro k; rfl
  | lit l => intro k; rfl
  | app f x ihf ihx =>
    intro k
    simp only [Setlec.Expr.abstract1, Setlec.Expr.instantiate1]
    rw [ihf k, ihx k]
  | lam n ty b m ihty ihb =>
    intro k
    simp only [Setlec.Expr.abstract1, Setlec.Expr.instantiate1]
    rw [ihty k, ihb (k + 1)]
  | forallE n ty b m ihty ihb =>
    intro k
    simp only [Setlec.Expr.abstract1, Setlec.Expr.instantiate1]
    rw [ihty k, ihb (k + 1)]
  | letE n ty v b ihty ihv ihb =>
    intro k
    simp only [Setlec.Expr.abstract1, Setlec.Expr.instantiate1]
    rw [ihty k, ihv k, ihb (k + 1)]
  | proj sn i e ih =>
    intro k
    simp only [Setlec.Expr.abstract1, Setlec.Expr.instantiate1]
    rw [ih k]

/-- The substitution's cursor is immaterial above the term's bvar
bound (closed values substitute the same at any cursor). -/
theorem substAK_cursor {d : Nat} {a : Expr} :
    ∀ {v : Expr} {j k k' : Nat},
      v.looseBVarsBounded j = true → j ≤ k → j ≤ k' →
      substAK d k a v = substAK d k' a v := by
  intro v
  induction v with
  | bvar i =>
    intro j k k' hb hk hk'
    simp only [Setlec.Expr.looseBVarsBounded,
      decide_eq_true_eq] at hb
    simp only [substAK, Setlec.Expr.abstract1,
      Setlec.Expr.instantiate1]
    rw [if_neg (by omega : ¬ (i = k)),
      if_neg (by omega : ¬ (i > k)),
      if_neg (by omega : ¬ (i = k')),
      if_neg (by omega : ¬ (i > k'))]
  | fvar idx n ty ih =>
    intro j k k' hb hk hk'
    simp only [substAK, Setlec.Expr.abstract1]
    by_cases h : idx = d
    · rw [if_pos h, if_pos h]
      simp [Setlec.Expr.instantiate1]
    · rw [if_neg h, if_neg h]
      rfl
  | sort u => intro j k k' hb hk hk'; rfl
  | const n us => intro j k k' hb hk hk'; rfl
  | lit l => intro j k k' hb hk hk'; rfl
  | app f x ihf ihx =>
    intro j k k' hb hk hk'
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    show Expr.app (substAK d k a f) (substAK d k a x)
        = Expr.app (substAK d k' a f) (substAK d k' a x)
    rw [ihf hb.1 hk hk', ihx hb.2 hk hk']
  | lam n ty b m ihty ihb =>
    intro j k k' hb hk hk'
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    show Expr.lam n (substAK d k a ty) (substAK d (k + 1) a b) m
        = Expr.lam n (substAK d k' a ty) (substAK d (k' + 1) a b) m
    rw [ihty hb.1 hk hk',
      ihb hb.2 (Nat.succ_le_succ hk) (Nat.succ_le_succ hk')]
  | forallE n ty b m ihty ihb =>
    intro j k k' hb hk hk'
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    show Expr.forallE n (substAK d k a ty)
        (substAK d (k + 1) a b) m
        = Expr.forallE n (substAK d k' a ty)
          (substAK d (k' + 1) a b) m
    rw [ihty hb.1 hk hk',
      ihb hb.2 (Nat.succ_le_succ hk) (Nat.succ_le_succ hk')]
  | letE n ty v' b ihty ihv ihb =>
    intro j k k' hb hk hk'
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    show Expr.letE n (substAK d k a ty) (substAK d k a v')
        (substAK d (k + 1) a b)
        = Expr.letE n (substAK d k' a ty) (substAK d k' a v')
          (substAK d (k' + 1) a b)
    rw [ihty hb.1.1 hk hk', ihv hb.1.2 hk hk',
      ihb hb.2 (Nat.succ_le_succ hk) (Nat.succ_le_succ hk')]
  | proj sn i e ih =>
    intro j k k' hb hk hk'
    simp only [Setlec.Expr.looseBVarsBounded] at hb
    show Expr.proj sn i (substAK d k a e)
        = Expr.proj sn i (substAK d k' a e)
    rw [ih hb hk hk']

/-- **The β/ζ composite** (the direct de Bruijn induction): the
telescope substitution commutes with one contraction — serves β
(where the value is additionally `substAK`-invariant) and ζ. -/
theorem substAK_instantiate1 {d : Nat} {a : Expr}
    (hab : a.looseBVarsBounded 0 = true)
    {v : Expr} (hvb : v.looseBVarsBounded 0 = true) :
    ∀ (b : Expr) (k : Nat),
      (substAK d (k + 1) a b).instantiate1 (substAK d k a v) k
        = substAK d k a (b.instantiate1 v k) := by
  intro b
  induction b with
  | bvar i =>
    intro k
    simp only [substAK, Setlec.Expr.abstract1,
      Setlec.Expr.instantiate1]
    by_cases h1 : i = k
    · subst h1
      rw [if_neg (by omega : ¬ (i = i + 1)),
        if_neg (by omega : ¬ (i > i + 1))]
      simp [Setlec.Expr.instantiate1]
    · by_cases h2 : i = k + 1
      · subst h2
        have e1 : (if k + 1 = k + 1 then a
            else if k + 1 > k + 1 then Expr.bvar (k + 1 - 1)
            else Expr.bvar (k + 1)) = a := by simp
        have e2 : (if k + 1 = k then v
            else if k + 1 > k then Expr.bvar (k + 1 - 1)
            else Expr.bvar (k + 1)) = Expr.bvar k := by
          rw [if_neg (by omega : ¬ (k + 1 = k)),
            if_pos (by omega : k + 1 > k)]
          rfl
        rw [e1, e2,
          show ((Expr.bvar k).abstract1 d k) = Expr.bvar k
            from rfl,
          show (Expr.bvar k).instantiate1 a k = a from by
            simp [Setlec.Expr.instantiate1]]
        exact Setlec.Expr.instantiate1_eq_self
          (looseBVarsBounded_mono (Nat.zero_le _) hab)
      · by_cases h3 : i > k
        · rw [if_neg h2, if_pos (by omega : i > k + 1),
            if_neg h1, if_pos h3]
          simp only [Setlec.Expr.instantiate1,
            Setlec.Expr.abstract1]
          simp only [if_neg (show ¬ (i - 1 = k) from by omega)]
        · rw [if_neg h2, if_neg (by omega : ¬ (i > k + 1)),
            if_neg h1, if_neg h3]
          simp only [Setlec.Expr.instantiate1,
            Setlec.Expr.abstract1]
          simp only [if_neg h1, if_neg h3]
  | fvar idx n ty ih =>
    intro k
    simp only [substAK, Setlec.Expr.abstract1,
      Setlec.Expr.instantiate1]
    by_cases h : idx = d
    · rw [if_pos h, if_pos h]
      simp only [Setlec.Expr.instantiate1]
      rw [if_pos trivial, if_pos trivial]
      exact Setlec.Expr.instantiate1_eq_self
        (looseBVarsBounded_mono (Nat.zero_le _) hab)
    · rw [if_neg h, if_neg h]
      rfl
  | sort u => intro k; rfl
  | const n us => intro k; rfl
  | lit l => intro k; rfl
  | app f x ihf ihx =>
    intro k
    show Expr.app
        ((substAK d (k + 1) a f).instantiate1 (substAK d k a v) k)
        ((substAK d (k + 1) a x).instantiate1 (substAK d k a v) k)
      = Expr.app (substAK d k a (f.instantiate1 v k))
        (substAK d k a (x.instantiate1 v k))
    rw [ihf k, ihx k]
  | lam n ty b m ihty ihb =>
    intro k
    show Expr.lam n
        ((substAK d (k + 1) a ty).instantiate1
          (substAK d k a v) k)
        ((substAK d (k + 2) a b).instantiate1
          (substAK d k a v) (k + 1)) m
      = Expr.lam n (substAK d k a (ty.instantiate1 v k))
        (substAK d (k + 1) a (b.instantiate1 v (k + 1))) m
    rw [ihty k]
    rw [show substAK d k a v = substAK d (k + 1) a v from
      substAK_cursor hvb (Nat.zero_le _) (Nat.zero_le _)]
    rw [ihb (k + 1)]
  | forallE n ty b m ihty ihb =>
    intro k
    show Expr.forallE n
        ((substAK d (k + 1) a ty).instantiate1
          (substAK d k a v) k)
        ((substAK d (k + 2) a b).instantiate1
          (substAK d k a v) (k + 1)) m
      = Expr.forallE n (substAK d k a (ty.instantiate1 v k))
        (substAK d (k + 1) a (b.instantiate1 v (k + 1))) m
    rw [ihty k]
    rw [show substAK d k a v = substAK d (k + 1) a v from
      substAK_cursor hvb (Nat.zero_le _) (Nat.zero_le _)]
    rw [ihb (k + 1)]
  | letE n ty v' b ihty ihv ihb =>
    intro k
    show Expr.letE n
        ((substAK d (k + 1) a ty).instantiate1
          (substAK d k a v) k)
        ((substAK d (k + 1) a v').instantiate1
          (substAK d k a v) k)
        ((substAK d (k + 2) a b).instantiate1
          (substAK d k a v) (k + 1))
      = Expr.letE n (substAK d k a (ty.instantiate1 v k))
        (substAK d k a (v'.instantiate1 v k))
        (substAK d (k + 1) a (b.instantiate1 v (k + 1)))
    rw [ihty k, ihv k]
    rw [show substAK d k a v = substAK d (k + 1) a v from
      substAK_cursor hvb (Nat.zero_le _) (Nat.zero_le _)]
    rw [ihb (k + 1)]
  | proj sn i e ih =>
    intro k
    show Expr.proj sn i
        ((substAK d (k + 1) a e).instantiate1
          (substAK d k a v) k)
      = Expr.proj sn i (substAK d k a (e.instantiate1 v k))
    rw [ih k]

/-- `mkAppN` distributes under `abstract1` (companion to
`mkAppN_instantiate1`; together they give `substAK_mkAppN`). -/
theorem mkAppN_abstract1 {d : Nat} :
    ∀ (args : List Expr) (h : Expr) (k : Nat),
      (Expr.mkAppN h args).abstract1 d k =
        Expr.mkAppN (h.abstract1 d k)
          (args.map (·.abstract1 d k)) := by
  intro args
  induction args with
  | nil => intro h k; rfl
  | cons x xs ih =>
    intro h k
    show (Expr.mkAppN (.app h x) xs).abstract1 d k = _
    rw [ih (.app h x) k]
    rfl

/-- **The ι composite's distribution law**: `substAK` distributes
over spines — the iota fire result (`mkAppN` of the closed rule RHS
over spine parts) maps under the telescope substitution to the fire
on the mapped spine (the RHS itself is `substAK`-invariant by
`substAK_eq_self` on env-stored closed terms). -/
theorem substAK_mkAppN {d k : Nat} {a : Expr} (h : Expr)
    (args : List Expr) :
    substAK d k a (Expr.mkAppN h args)
      = Expr.mkAppN (substAK d k a h)
          (args.map (substAK d k a)) := by
  unfold substAK
  rw [mkAppN_abstract1, Setlec.Expr.mkAppN_instantiate1,
    List.map_map]
  rfl

end Discharge

end Setlec.SetR.Interp2
