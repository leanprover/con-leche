import Setlec.SetR.Annot.SortCoh.Align

/-!
# The Θ relation and the θ-lock statement tier (the corrected
architecture's map)

Per the ratified round-three correction: the summit discharge is an
inline induction down the given loops' core runs at ZipBelow's own
bar, with the telescope as traveling data.  `ThetaRel` closes the
zip tier's relation over the traveling material — three rows:

* `zip` — the landed tier's currency (the discharge DELEGATES to
  the landed `coreLock` here and embeds its out);
* `packed` — a pending defeq run on OPENED cores under the
  telescope images (knot decoupled from the tier, the round-three
  finding), spines staying `CertZip (T+1)` (congruence-arm argument
  pairs lift by fuel monotonicity — no nesting);
* `same` — a SHARED opened core under both telescope images (the
  syn material; analyzed by core shape, its in-zone leaves exiting
  through the entries' own zips).

The θ-lock outs mirror the landed `CoreSeam`/`LoopSeamOut` shapes
with `ThetaRel`-material where the landed rows carried zips.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec (CheckMode Env Expr Name Level inferTypeCore whnf whnfCore
  isDefEqCore unfoldDefinition)

section Discharge
variable {μ : CheckMode} {env : Env}

/-- `CertZip` lifts along the certificate fuel. -/
theorem certZip_mono (hm : KnotFuelMono μ env)
    {fc fc' d : Nat} (hfc : fc ≤ fc') {a b : Expr}
    (h : CertZip μ env fc d a b) : CertZip μ env fc' d a b := by
  induction h with
  | refl e => exact .refl e
  | cert a b hba hbb hc => exact .cert a b hba hbb (hm.2.2.2.1 hfc hc)
  | sortSlack u v hev => exact .sortSlack u v hev
  | constSlack n us us' hev => exact .constSlack n us us' hev
  | fvar i n ty₁ ty₂ hty ih => exact .fvar i n ty₁ ty₂ ih
  | app f₁ a₁ f₂ a₂ hf ha ihf iha => exact .app f₁ a₁ f₂ a₂ ihf iha
  | lam n ty₁ ty₂ b₁ b₂ m hty hb iht ihb =>
    exact .lam n ty₁ ty₂ b₁ b₂ m iht ihb
  | forallE n ty₁ ty₂ b₁ b₂ m hty hb iht ihb =>
    exact .forallE n ty₁ ty₂ b₁ b₂ m iht ihb
  | letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hv hb iht ihv ihb =>
    exact .letE n ty₁ ty₂ v₁ v₂ b₁ b₂ iht ihv ihb
  | proj s i e₁ e₂ he ih => exact .proj s i e₁ e₂ ih

/-- **The Θ relation** at telescope tier `T`, depth `d`: the
traveling currency of the corrected architecture. -/
inductive ThetaRel (μ : CheckMode) (env : Env) (T d : Nat) :
    Expr → Expr → Prop
  | zip {fc' : Nat} {a b : Expr}
      (hfc : fc' ≤ T + 1)
      (hz : CertZip μ env fc' d a b) :
      ThetaRel μ env T d a b
  | packed {Γ : List ThetaEntry} {k L : Nat} {C₁ C₂ : Expr}
      {sp₁ sp₂ : List Expr}
      (hT : TelescopeOk μ env T d Γ)
      (hk : k ≤ T)
      (hrun : Setlec.defeqLoop μ (Setlec.pureFns μ env k) env
        (d + Γ.length) L C₁ C₂ = .ok true)
      (hlen : sp₁.length = sp₂.length)
      (hsp : ∀ i (h₁ : i < sp₁.length) (h₂ : i < sp₂.length),
        CertZip μ env (T + 1) d sp₁[i] sp₂[i]) :
      ThetaRel μ env T d
        (Setlec.Expr.mkAppN (thetaSubst₁ d Γ C₁) sp₁)
        (Setlec.Expr.mkAppN (thetaSubst₂ d Γ C₂) sp₂)
  | same {Γ : List ThetaEntry} {P : Expr} {sp₁ sp₂ : List Expr}
      (hT : TelescopeOk μ env T d Γ)
      (hlen : sp₁.length = sp₂.length)
      (hsp : ∀ i (h₁ : i < sp₁.length) (h₂ : i < sp₂.length),
        CertZip μ env (T + 1) d sp₁[i] sp₂[i]) :
      ThetaRel μ env T d
        (Setlec.Expr.mkAppN (thetaSubst₁ d Γ P) sp₁)
        (Setlec.Expr.mkAppN (thetaSubst₂ d Γ P) sp₂)

/-- **The θ core seam** — the landed `CoreSeam`'s shape with
`ThetaRel` material at the head rows (the dead rows verbatim). -/
inductive ThetaCoreSeam (μ : CheckMode) (env : Env) (T d : Nat) :
    Expr → Expr → Prop
  | rel {w₁ w₂ : Expr} (h : ThetaRel μ env T d w₁ w₂) :
      ThetaCoreSeam μ env T d w₁ w₂
  | certHead (F₁ F₂ : Expr) (fc' : Nat) (as bs : List Expr)
      (hfc : fc' ≤ T + 1)
      (hba : F₁.looseBVarsBounded 0 = true)
      (hbb : F₂.looseBVarsBounded 0 = true)
      (hc : isDefEqCore μ env fc' d F₁ F₂ = .ok true)
      (hlen : as.length = bs.length)
      (hargs : ∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        ThetaRel μ env T d as[i] bs[i]) :
      ThetaCoreSeam μ env T d (Setlec.Expr.mkAppN F₁ as)
        (Setlec.Expr.mkAppN F₂ bs)
  | recHead (n : Name) (cv : Setlec.ConstantVal) (mI rP : Nat)
      (rules : List Setlec.RecRule) (us us' : List Level)
      (as bs : List Expr)
      (hf : env.find? n = some (.recInfo cv mI rP rules))
      (hev : ∀ φ' : Name → Nat,
        us.map (Level.eval φ') = us'.map (Level.eval φ'))
      (hlen : as.length = bs.length)
      (hargs : ∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        ThetaRel μ env T d as[i] bs[i]) :
      ThetaCoreSeam μ env T d
        (Setlec.Expr.mkAppN (.const n us) as)
        (Setlec.Expr.mkAppN (.const n us') bs)
  | projHead (sn : Name) (i : Nat) (e₁ e₂ : Expr)
      (as bs : List Expr)
      (he : ThetaRel μ env T d e₁ e₂)
      (hlen : as.length = bs.length)
      (hargs : ∀ j (h₁ : j < as.length) (h₂ : j < bs.length),
        ThetaRel μ env T d as[j] bs[j]) :
      ThetaCoreSeam μ env T d
        (Setlec.Expr.mkAppN (.proj sn i e₁) as)
        (Setlec.Expr.mkAppN (.proj sn i e₂) bs)
  | deadL (u v u' : Expr) (b : Nat)
      (hrun : ∀ g, b ≤ g → whnfCore μ env g d u = .ok u')
      (hnc : ∀ p q, u'.getAppFn ≠ .const p q)
      (hnl : ∀ n ty body m, u' ≠ .lam n ty body m)
      (hns : ∀ ℓ, u' ≠ .sort ℓ) :
      ThetaCoreSeam μ env T d u v
  | deadR (u v v' : Expr) (b : Nat)
      (hrun : ∀ g, b ≤ g → whnfCore μ env g d v = .ok v')
      (hnc : ∀ p q, v'.getAppFn ≠ .const p q)
      (hnl : ∀ n ty body m, v' ≠ .lam n ty body m)
      (hns : ∀ ℓ, v' ≠ .sort ℓ) :
      ThetaCoreSeam μ env T d u v
  | alignSeam (G : Nat)
      (h : FireSeam μ env d G ∨ ProjSeam μ env d G ∨
        ConvSeam μ env d G ∨ NatSeam μ env d G) :
      ∀ {u v : Expr}, ThetaCoreSeam μ env T d u v

/-- **The θ core lock's conclusion**: the pair's core outputs are
`ThetaRel`-related again, or a `Contracts`-rebased pair sits at a
θ seam (the landed shape with the traveling material). -/
def ThetaCoreOut (μ : CheckMode) (env : Env) (T d : Nat)
    (g₁ g₂ : Nat) (u v u' v' : Expr) : Prop :=
  (ThetaRel μ env T d u' v' ∧ SubjInv d u' ∧ SubjInv d v' ∧
    PairedLeaves u' v') ∨
  (∃ w₁ w₂ c₁ c₂, c₁ ≤ g₁ ∧ c₂ ≤ g₂ ∧
    whnfCore μ env c₁ d w₁ = .ok u' ∧
    whnfCore μ env c₂ d w₂ = .ok v' ∧
    Contracts μ env d u w₁ ∧ Contracts μ env d v w₂ ∧
    ThetaCoreSeam μ env T d w₁ w₂)

/-- **The θ core lock claim** (statement tier; the discharge is the
inline induction on the given runs' knot sum, delegating to the
landed `coreLock` at zip rows). -/
def ThetaCoreLockF (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ (N : Nat) {g₁ g₂ T d : Nat} {u v u' v' : Expr},
    g₁ + g₂ ≤ N →
    ThetaRel μ env T d u v →
    SubjInv d u → SubjInv d v →
    PairedLeaves u v → Q d u v →
    whnfCore μ env g₁ d u = .ok u' →
    whnfCore μ env g₂ d v = .ok v' →
    ThetaCoreOut μ env T d g₁ g₂ u v u' v'

/-! ### The θ-substitution computation kit -/

/-- `thetaSubst₁` is the identity on sorts. -/
theorem thetaSubst₁_sort {d : Nat} {u : Level} :
    ∀ {Γ : List ThetaEntry}, thetaSubst₁ d Γ (.sort u) = .sort u
  | [] => rfl
  | t :: Γ' => by
    show substAK d 0 t.a₁ (thetaSubst₁ (d + 1) Γ' (.sort u)) = _
    rw [thetaSubst₁_sort (Γ := Γ')]
    rfl

/-- `thetaSubst₂` is the identity on sorts. -/
theorem thetaSubst₂_sort {d : Nat} {u : Level} :
    ∀ {Γ : List ThetaEntry}, thetaSubst₂ d Γ (.sort u) = .sort u
  | [] => rfl
  | t :: Γ' => by
    show substAK d 0 t.a₂ (thetaSubst₂ (d + 1) Γ' (.sort u)) = _
    rw [thetaSubst₂_sort (Γ := Γ')]
    rfl

/-- `thetaSubst₁` is the identity on constants. -/
theorem thetaSubst₁_const {d : Nat} {c : Name} {us : List Level} :
    ∀ {Γ : List ThetaEntry}, thetaSubst₁ d Γ (.const c us)
      = .const c us
  | [] => rfl
  | t :: Γ' => by
    show substAK d 0 t.a₁ (thetaSubst₁ (d + 1) Γ' (.const c us)) = _
    rw [thetaSubst₁_const (Γ := Γ')]
    rfl

/-- `thetaSubst₂` is the identity on constants. -/
theorem thetaSubst₂_const {d : Nat} {c : Name} {us : List Level} :
    ∀ {Γ : List ThetaEntry}, thetaSubst₂ d Γ (.const c us)
      = .const c us
  | [] => rfl
  | t :: Γ' => by
    show substAK d 0 t.a₂ (thetaSubst₂ (d + 1) Γ' (.const c us)) = _
    rw [thetaSubst₂_const (Γ := Γ')]
    rfl

/-- `thetaSubst₁` is the identity on literals. -/
theorem thetaSubst₁_lit {d : Nat} {v : Setlec.Literal} :
    ∀ {Γ : List ThetaEntry}, thetaSubst₁ d Γ (.lit v) = .lit v
  | [] => rfl
  | t :: Γ' => by
    show substAK d 0 t.a₁ (thetaSubst₁ (d + 1) Γ' (.lit v)) = _
    rw [thetaSubst₁_lit (Γ := Γ')]
    rfl

/-- `thetaSubst₂` is the identity on literals. -/
theorem thetaSubst₂_lit {d : Nat} {v : Setlec.Literal} :
    ∀ {Γ : List ThetaEntry}, thetaSubst₂ d Γ (.lit v) = .lit v
  | [] => rfl
  | t :: Γ' => by
    show substAK d 0 t.a₂ (thetaSubst₂ (d + 1) Γ' (.lit v)) = _
    rw [thetaSubst₂_lit (Γ := Γ')]
    rfl

/-- `thetaSubst₁` distributes over applications. -/
theorem thetaSubst₁_app {d : Nat} {f a : Expr} :
    ∀ {Γ : List ThetaEntry}, thetaSubst₁ d Γ (.app f a)
      = .app (thetaSubst₁ d Γ f) (thetaSubst₁ d Γ a)
  | [] => rfl
  | t :: Γ' => by
    show substAK d 0 t.a₁ (thetaSubst₁ (d + 1) Γ' (.app f a)) = _
    rw [thetaSubst₁_app (Γ := Γ')]
    rfl

/-- `thetaSubst₂` distributes over applications. -/
theorem thetaSubst₂_app {d : Nat} {f a : Expr} :
    ∀ {Γ : List ThetaEntry}, thetaSubst₂ d Γ (.app f a)
      = .app (thetaSubst₂ d Γ f) (thetaSubst₂ d Γ a)
  | [] => rfl
  | t :: Γ' => by
    show substAK d 0 t.a₂ (thetaSubst₂ (d + 1) Γ' (.app f a)) = _
    rw [thetaSubst₂_app (Γ := Γ')]
    rfl

/-- Abstracting a fresh opening recovers the body (the reverse
roundtrip; the push-algebra's core). -/
theorem instantiate1_abstract1_fresh {D : Nat} {n : Name}
    {ty : Expr} :
    ∀ {e : Expr} {k : Nat},
      (∀ l ∈ e.fvarLeaves, l.1 ≠ D) →
      e.looseBVarsBounded (k + 1) = true →
      (e.instantiate1 (.fvar D n ty) k).abstract1 D k = e := by
  intro e
  induction e with
  | bvar i =>
    intro k hf hb
    simp only [Setlec.Expr.looseBVarsBounded,
      decide_eq_true_eq] at hb
    simp only [Setlec.Expr.instantiate1]
    by_cases h1 : i = k
    · rw [if_pos h1]
      show (if D = D then Expr.bvar k else _) = _
      rw [if_pos rfl, h1]
    · rw [if_neg h1, if_neg (by omega : ¬ i > k)]
      rfl
  | fvar idx nm ty' ih =>
    intro k hf hb
    simp only [Setlec.Expr.instantiate1, Setlec.Expr.abstract1]
    have hne : idx ≠ D := hf (idx, nm, ty') (by
      simp [Setlec.Expr.fvarLeaves])
    rw [if_neg hne]
  | sort u => intro k hf hb; rfl
  | const c us => intro k hf hb; rfl
  | lit v => intro k hf hb; rfl
  | app f a ihf iha =>
    intro k hf hb
    simp only [Setlec.Expr.looseBVarsBounded,
      Bool.and_eq_true] at hb
    show Expr.app _ _ = _
    rw [ihf (fun l hl => hf l (by
        simp only [Setlec.Expr.fvarLeaves, List.mem_append]
        exact Or.inl hl)) hb.1,
      iha (fun l hl => hf l (by
        simp only [Setlec.Expr.fvarLeaves, List.mem_append]
        exact Or.inr hl)) hb.2]
  | lam nm ty' b m iht ihb =>
    intro k hf hb
    simp only [Setlec.Expr.looseBVarsBounded,
      Bool.and_eq_true] at hb
    show Expr.lam nm _ _ m = _
    rw [iht (fun l hl => hf l (by
        simp only [Setlec.Expr.fvarLeaves, List.mem_append]
        exact Or.inl hl)) hb.1,
      ihb (fun l hl => hf l (by
        simp only [Setlec.Expr.fvarLeaves, List.mem_append]
        exact Or.inr hl)) hb.2]
  | forallE nm ty' b m iht ihb =>
    intro k hf hb
    simp only [Setlec.Expr.looseBVarsBounded,
      Bool.and_eq_true] at hb
    show Expr.forallE nm _ _ m = _
    rw [iht (fun l hl => hf l (by
        simp only [Setlec.Expr.fvarLeaves, List.mem_append]
        exact Or.inl hl)) hb.1,
      ihb (fun l hl => hf l (by
        simp only [Setlec.Expr.fvarLeaves, List.mem_append]
        exact Or.inr hl)) hb.2]
  | letE nm ty' v b iht ihv ihb =>
    intro k hf hb
    simp only [Setlec.Expr.looseBVarsBounded,
      Bool.and_eq_true] at hb
    show Expr.letE nm _ _ _ = _
    rw [iht (fun l hl => hf l (by
        simp only [Setlec.Expr.fvarLeaves, List.mem_append]
        exact Or.inl (Or.inl hl))) hb.1.1,
      ihv (fun l hl => hf l (by
        simp only [Setlec.Expr.fvarLeaves, List.mem_append]
        exact Or.inl (Or.inr hl))) hb.1.2,
      ihb (fun l hl => hf l (by
        simp only [Setlec.Expr.fvarLeaves, List.mem_append]
        exact Or.inr hl)) hb.2]
  | proj sn i e ih =>
    intro k hf hb
    show Expr.proj sn i _ = _
    rw [ih (fun l hl => hf l (by
        simpa only [Setlec.Expr.fvarLeaves] using hl)) hb]

/-- The telescope substitution folds over append (LEFT side). -/
theorem thetaSubst₁_append {d : Nat} {t : ThetaEntry} :
    ∀ {Γ : List ThetaEntry} {e : Expr},
      thetaSubst₁ d (Γ ++ [t]) e
        = thetaSubst₁ d Γ
            (substAK (d + Γ.length) 0 t.a₁ e)
  | [], e => by
    show substAK d 0 t.a₁ (thetaSubst₁ (d + 1) [] e) = _
    rfl
  | t' :: Γ', e => by
    show substAK d 0 t'.a₁ (thetaSubst₁ (d + 1) (Γ' ++ [t]) e) = _
    rw [thetaSubst₁_append (Γ := Γ')]
    show _ = substAK d 0 t'.a₁
      (thetaSubst₁ (d + 1) Γ'
        (substAK (d + (Γ'.length + 1)) 0 t.a₁ e))
    have : (d + 1) + Γ'.length = d + (Γ'.length + 1) := by omega
    rw [this]

/-- The telescope substitution folds over append (RIGHT side). -/
theorem thetaSubst₂_append {d : Nat} {t : ThetaEntry} :
    ∀ {Γ : List ThetaEntry} {e : Expr},
      thetaSubst₂ d (Γ ++ [t]) e
        = thetaSubst₂ d Γ
            (substAK (d + Γ.length) 0 t.a₂ e)
  | [], e => by
    show substAK d 0 t.a₂ (thetaSubst₂ (d + 1) [] e) = _
    rfl
  | t' :: Γ', e => by
    show substAK d 0 t'.a₂ (thetaSubst₂ (d + 1) (Γ' ++ [t]) e) = _
    rw [thetaSubst₂_append (Γ := Γ')]
    show _ = substAK d 0 t'.a₂
      (thetaSubst₂ (d + 1) Γ'
        (substAK (d + (Γ'.length + 1)) 0 t.a₂ e))
    have : (d + 1) + Γ'.length = d + (Γ'.length + 1) := by omega
    rw [this]

/-- The telescope's per-entry facts fold over append. -/
theorem TelescopeOk.append {T : Nat} {t : ThetaEntry} :
    ∀ {Γ : List ThetaEntry} {d : Nat},
      TelescopeOk μ env T d Γ →
      CertZip μ env (T + 1) (d + Γ.length) t.a₁ t.a₂ →
      isDefEqCore μ env (T + 1) (d + Γ.length) t.ty₁ t.ty₂
        = .ok true →
      SubjInv (d + Γ.length) t.a₁ →
      SubjInv (d + Γ.length) t.a₂ →
      PairedLeaves t.a₁ t.a₂ →
      TelescopeOk μ env T d (Γ ++ [t])
  | [], d => fun _ hz hd hI₁ hI₂ hp =>
    ⟨hz, hd, hI₁, hI₂, hp, trivial⟩
  | t' :: Γ', d => fun hΓ hz hd hI₁ hI₂ hp => by
    obtain ⟨hz', hd', hI₁', hI₂', hp', hΓ''⟩ := hΓ
    have heq : (d + 1) + Γ'.length = d + (Γ'.length + 1) := by
      omega
    exact ⟨hz', hd', hI₁', hI₂', hp',
      TelescopeOk.append hΓ'' (heq ▸ hz) (heq ▸ hd) (heq ▸ hI₁)
        (heq ▸ hI₂) hp⟩

/-- The telescope substitution is the identity on outer-scoped
closed terms (every level's `substAK` is `substAK_eq_self`). -/
theorem thetaSubst₁_scoped_id :
    ∀ {Γ : List ThetaEntry} {d : Nat} {e : Expr},
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      thetaSubst₁ d Γ e = e
  | [], d, e => fun _ _ => rfl
  | t :: Γ', d, e => fun hw hb => by
    show substAK d 0 t.a₁ (thetaSubst₁ (d + 1) Γ' e) = e
    rw [thetaSubst₁_scoped_id (Γ := Γ')
      (Setlec.Expr.WScoped.mono (Nat.le_succ d) hw) hb]
    exact substAK_eq_self
      (fun l hl => Nat.ne_of_lt
        (Setlec.Expr.fvarLeaves_lt_of_wscoped hw l hl)) hb

/-- RIGHT-side version. -/
theorem thetaSubst₂_scoped_id :
    ∀ {Γ : List ThetaEntry} {d : Nat} {e : Expr},
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      thetaSubst₂ d Γ e = e
  | [], d, e => fun _ _ => rfl
  | t :: Γ', d, e => fun hw hb => by
    show substAK d 0 t.a₂ (thetaSubst₂ (d + 1) Γ' e) = e
    rw [thetaSubst₂_scoped_id (Γ := Γ')
      (Setlec.Expr.WScoped.mono (Nat.le_succ d) hw) hb]
    exact substAK_eq_self
      (fun l hl => Nat.ne_of_lt
        (Setlec.Expr.fvarLeaves_lt_of_wscoped hw l hl)) hb

/-- The λ-image's shape and its β composite (LEFT). -/
theorem thetaSubst₁_lam_beta {T : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat} {n : Name} {ty b : Expr}
      {m : Setlec.BinderMeta},
      TelescopeOk μ env T d Γ →
      ∃ TY B, thetaSubst₁ d Γ (.lam n ty b m) = .lam n TY B m ∧
        ∀ x, x.looseBVarsBounded 0 = true →
          B.instantiate1 (thetaSubst₁ d Γ x)
            = thetaSubst₁ d Γ (b.instantiate1 x)
  | [], d, n, ty, b, m => fun _ => ⟨ty, b, rfl, fun x hx => rfl⟩
  | t :: Γ', d, n, ty, b, m => fun hΓ => by
    obtain ⟨hz, hd, hI₁, hI₂, hp, hΓ'⟩ := hΓ
    obtain ⟨TY', B', hshape, hbeta⟩ :=
      thetaSubst₁_lam_beta (Γ := Γ') (d := d + 1) (n := n)
        (ty := ty) (b := b) (m := m) hΓ'
    refine ⟨substAK d 0 t.a₁ TY', substAK d 1 t.a₁ B', ?_, ?_⟩
    · show substAK d 0 t.a₁
        (thetaSubst₁ (d + 1) Γ' (.lam n ty b m)) = _
      rw [hshape]
      rfl
    · intro x hx
      show (substAK d 1 t.a₁ B').instantiate1
        (substAK d 0 t.a₁ (thetaSubst₁ (d + 1) Γ' x)) = _
      rw [substAK_instantiate1 hI₁.2.1
        (thetaSubst_bounded₁ hΓ' hx) B' 0, hbeta x hx]
      rfl

/-- The λ-image's shape and its β composite (RIGHT). -/
theorem thetaSubst₂_lam_beta {T : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat} {n : Name} {ty b : Expr}
      {m : Setlec.BinderMeta},
      TelescopeOk μ env T d Γ →
      ∃ TY B, thetaSubst₂ d Γ (.lam n ty b m) = .lam n TY B m ∧
        ∀ x, x.looseBVarsBounded 0 = true →
          B.instantiate1 (thetaSubst₂ d Γ x)
            = thetaSubst₂ d Γ (b.instantiate1 x)
  | [], d, n, ty, b, m => fun _ => ⟨ty, b, rfl, fun x hx => rfl⟩
  | t :: Γ', d, n, ty, b, m => fun hΓ => by
    obtain ⟨hz, hd, hI₁, hI₂, hp, hΓ'⟩ := hΓ
    obtain ⟨TY', B', hshape, hbeta⟩ :=
      thetaSubst₂_lam_beta (Γ := Γ') (d := d + 1) (n := n)
        (ty := ty) (b := b) (m := m) hΓ'
    refine ⟨substAK d 0 t.a₂ TY', substAK d 1 t.a₂ B', ?_, ?_⟩
    · show substAK d 0 t.a₂
        (thetaSubst₂ (d + 1) Γ' (.lam n ty b m)) = _
      rw [hshape]
      rfl
    · intro x hx
      show (substAK d 1 t.a₂ B').instantiate1
        (substAK d 0 t.a₂ (thetaSubst₂ (d + 1) Γ' x)) = _
      rw [substAK_instantiate1 hI₂.2.1
        (thetaSubst_bounded₂ hΓ' hx) B' 0, hbeta x hx]
      rfl

/-- **The push algebra** (LEFT): the θ-image of the pushed opened
body IS the actual β-contractum. -/
theorem thetaSubst₁_push {T : Nat} {Γ : List ThetaEntry} {d : Nat}
    {n : Name} {ty b TY B x : Expr} {m : Setlec.BinderMeta}
    {t : ThetaEntry}
    (_hΓ : TelescopeOk μ env T d Γ)
    (_hshape : thetaSubst₁ d Γ (.lam n ty b m) = .lam n TY B m)
    (hbeta : ∀ y, y.looseBVarsBounded 0 = true →
      B.instantiate1 (thetaSubst₁ d Γ y)
        = thetaSubst₁ d Γ (b.instantiate1 y))
    (ha : t.a₁ = x)
    (hxw : Expr.WScoped d x) (hxb : x.looseBVarsBounded 0 = true)
    (hbf : ∀ l ∈ b.fvarLeaves, l.1 ≠ d + Γ.length)
    (hbb : b.looseBVarsBounded 1 = true) :
    thetaSubst₁ d (Γ ++ [t])
      (b.instantiate1 (.fvar (d + Γ.length) t.n₁ t.ty₁))
      = B.instantiate1 x := by
  rw [thetaSubst₁_append]
  rw [show substAK (d + Γ.length) 0 t.a₁
      (b.instantiate1 (.fvar (d + Γ.length) t.n₁ t.ty₁))
      = b.instantiate1 t.a₁ from by
    unfold substAK
    rw [instantiate1_abstract1_fresh hbf hbb]]
  rw [ha, ← hbeta x hxb, thetaSubst₁_scoped_id hxw hxb]

/-- The telescope substitution distributes over spines (LEFT). -/
theorem thetaSubst₁_mkAppN {d : Nat} {Γ : List ThetaEntry} :
    ∀ (as : List Expr) (H : Expr),
      thetaSubst₁ d Γ (Setlec.Expr.mkAppN H as)
        = Setlec.Expr.mkAppN (thetaSubst₁ d Γ H)
            (as.map (thetaSubst₁ d Γ))
  | [], H => rfl
  | a :: as, H => by
    show thetaSubst₁ d Γ (Setlec.Expr.mkAppN (.app H a) as) = _
    rw [thetaSubst₁_mkAppN as (.app H a), thetaSubst₁_app]
    rfl

/-- The telescope substitution distributes over spines (RIGHT). -/
theorem thetaSubst₂_mkAppN {d : Nat} {Γ : List ThetaEntry} :
    ∀ (as : List Expr) (H : Expr),
      thetaSubst₂ d Γ (Setlec.Expr.mkAppN H as)
        = Setlec.Expr.mkAppN (thetaSubst₂ d Γ H)
            (as.map (thetaSubst₂ d Γ))
  | [], H => rfl
  | a :: as, H => by
    show thetaSubst₂ d Γ (Setlec.Expr.mkAppN (.app H a) as) = _
    rw [thetaSubst₂_mkAppN as (.app H a), thetaSubst₂_app]
    rfl

/-- The Π-image's shape (LEFT; the refutation arms only need the
constructor). -/
theorem thetaSubst₁_forallE {d : Nat} {n : Name} {ty b : Expr}
    {m : Setlec.BinderMeta} :
    ∀ {Γ : List ThetaEntry},
      ∃ TY B, thetaSubst₁ d Γ (.forallE n ty b m)
        = .forallE n TY B m
  | [] => ⟨ty, b, rfl⟩
  | t :: Γ' => by
    obtain ⟨TY', B', hs⟩ := thetaSubst₁_forallE (Γ := Γ')
      (d := d + 1) (n := n) (ty := ty) (b := b) (m := m)
    refine ⟨substAK d 0 t.a₁ TY', substAK d 1 t.a₁ B', ?_⟩
    show substAK d 0 t.a₁
      (thetaSubst₁ (d + 1) Γ' (.forallE n ty b m)) = _
    rw [hs]
    rfl

/-- The Π-image's shape (RIGHT). -/
theorem thetaSubst₂_forallE {d : Nat} {n : Name} {ty b : Expr}
    {m : Setlec.BinderMeta} :
    ∀ {Γ : List ThetaEntry},
      ∃ TY B, thetaSubst₂ d Γ (.forallE n ty b m)
        = .forallE n TY B m
  | [] => ⟨ty, b, rfl⟩
  | t :: Γ' => by
    obtain ⟨TY', B', hs⟩ := thetaSubst₂_forallE (Γ := Γ')
      (d := d + 1) (n := n) (ty := ty) (b := b) (m := m)
    refine ⟨substAK d 0 t.a₂ TY', substAK d 1 t.a₂ B', ?_⟩
    show substAK d 0 t.a₂
      (thetaSubst₂ (d + 1) Γ' (.forallE n ty b m)) = _
    rw [hs]
    rfl

/-- The proj-image distributes (LEFT). -/
theorem thetaSubst₁_proj {d : Nat} {sn : Name} {i : Nat}
    {e : Expr} :
    ∀ {Γ : List ThetaEntry},
      thetaSubst₁ d Γ (.proj sn i e)
        = .proj sn i (thetaSubst₁ d Γ e)
  | [] => rfl
  | t :: Γ' => by
    show substAK d 0 t.a₁ (thetaSubst₁ (d + 1) Γ' (.proj sn i e))
      = _
    rw [thetaSubst₁_proj (Γ := Γ')]
    rfl

/-- The proj-image distributes (RIGHT). -/
theorem thetaSubst₂_proj {d : Nat} {sn : Name} {i : Nat}
    {e : Expr} :
    ∀ {Γ : List ThetaEntry},
      thetaSubst₂ d Γ (.proj sn i e)
        = .proj sn i (thetaSubst₂ d Γ e)
  | [] => rfl
  | t :: Γ' => by
    show substAK d 0 t.a₂ (thetaSubst₂ (d + 1) Γ' (.proj sn i e))
      = _
    rw [thetaSubst₂_proj (Γ := Γ')]
    rfl

end Discharge

end Setlec.SetR.Interp2
