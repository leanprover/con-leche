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

end Discharge

end Setlec.SetR.Interp2
