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

mutual
/-- **The Θ relation, as data** (round three — Type-valued so the
in-zone chase recurses on honest sub-terms; the spines are the
mutual list so `sizeOf` counts them).  A pair is Θ-related when
both sides are telescope images of zip-related, run-related, or
SHARED cores over Θ-related spines. -/
inductive ThetaRelD (μ : CheckMode) (env : Env) (T : Nat) :
    Nat → Expr → Expr → Type
  | zipCore {d : Nat} {Γ : List ThetaEntry} {fc' : Nat}
      {A₁ A₂ : Expr} {sp₁ sp₂ : List Expr}
      (hT : TelescopeRelD μ env T d Γ)
      (hfc : fc' ≤ T + 1)
      (hz : CertZip μ env fc' (d + Γ.length) A₁ A₂)
      (hC₁ : SubjInv (d + Γ.length) A₁)
      (hC₂ : SubjInv (d + Γ.length) A₂)
      (hsp : ThetaRelsD μ env T d sp₁ sp₂) :
      ThetaRelD μ env T d
        (Setlec.Expr.mkAppN (thetaSubst₁ d Γ A₁) sp₁)
        (Setlec.Expr.mkAppN (thetaSubst₂ d Γ A₂) sp₂)
  | runCore {d : Nat} {Γ : List ThetaEntry} {k L : Nat}
      {C₁ C₂ : Expr} {sp₁ sp₂ : List Expr}
      (hT : TelescopeRelD μ env T d Γ)
      (hk : k ≤ T)
      (hrun : Setlec.defeqLoop μ (Setlec.pureFns μ env k) env
        (d + Γ.length) L C₁ C₂ = .ok true)
      (hC₁ : SubjInv (d + Γ.length) C₁)
      (hC₂ : SubjInv (d + Γ.length) C₂)
      (hsp : ThetaRelsD μ env T d sp₁ sp₂) :
      ThetaRelD μ env T d
        (Setlec.Expr.mkAppN (thetaSubst₁ d Γ C₁) sp₁)
        (Setlec.Expr.mkAppN (thetaSubst₂ d Γ C₂) sp₂)
  | sameCore {d : Nat} {Γ : List ThetaEntry} {P : Expr}
      {sp₁ sp₂ : List Expr}
      (hT : TelescopeRelD μ env T d Γ)
      (hP : SubjInv (d + Γ.length) P)
      (hsp : ThetaRelsD μ env T d sp₁ sp₂) :
      ThetaRelD μ env T d
        (Setlec.Expr.mkAppN (thetaSubst₁ d Γ P) sp₁)
        (Setlec.Expr.mkAppN (thetaSubst₂ d Γ P) sp₂)

/-- Θ-related spines, as data. -/
inductive ThetaRelsD (μ : CheckMode) (env : Env) (T : Nat) :
    Nat → List Expr → List Expr → Type
  | nil {d : Nat} : ThetaRelsD μ env T d [] []
  | cons {d : Nat} {a b : Expr} {as bs : List Expr}
      (h : ThetaRelD μ env T d a b)
      (rest : ThetaRelsD μ env T d as bs) :
      ThetaRelsD μ env T d (a :: as) (b :: bs)

/-- **The Θ telescope, as data**. -/
inductive TelescopeRelD (μ : CheckMode) (env : Env) (T : Nat) :
    Nat → List ThetaEntry → Type
  | nil {d : Nat} : TelescopeRelD μ env T d []
  | cons {d : Nat} {t : ThetaEntry} {Γ : List ThetaEntry}
      (hz : ThetaRelD μ env T d t.a₁ t.a₂)
      (hd : ThetaRelD μ env T d t.ty₁ t.ty₂)
      (hI₁ : SubjInv d t.a₁) (hI₂ : SubjInv d t.a₂)
      (hp : PairedLeaves t.a₁ t.a₂)
      (rest : TelescopeRelD μ env T (d + 1) Γ) :
      TelescopeRelD μ env T d (t :: Γ)
end

/-- The Prop-level Θ relation (the statements' currency). -/
def ThetaRel (μ : CheckMode) (env : Env) (T d : Nat)
    (a b : Expr) : Prop :=
  Nonempty (ThetaRelD μ env T d a b)

/-- The Prop-level Θ telescope. -/
def TelescopeRel (μ : CheckMode) (env : Env) (T d : Nat)
    (Γ : List ThetaEntry) : Prop :=
  Nonempty (TelescopeRelD μ env T d Γ)

/-- Spine lengths agree. -/
theorem ThetaRelsD.length_eq {T d : Nat} :
    ∀ {as bs : List Expr}, ThetaRelsD μ env T d as bs →
      as.length = bs.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ rest => by
    simp [ThetaRelsD.length_eq rest]

/-- Spine member relations. -/
theorem ThetaRelsD.get {T d : Nat} :
    ∀ {as bs : List Expr}, ThetaRelsD μ env T d as bs →
      ∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        ThetaRel μ env T d as[i] bs[i]
  | [], [], .nil => fun i h₁ h₂ => absurd h₁ (by simp)
  | _ :: _, _ :: _, .cons h rest => fun i h₁ h₂ =>
    match i with
    | 0 => ⟨h⟩
    | i + 1 => ThetaRelsD.get rest i (by simpa using h₁)
        (by simpa using h₂)

/-- A bare zip is `zipCore` at the empty telescope and spine
(data form). -/
def ThetaRelD.ofZip {T d fc' : Nat} {a b : Expr}
    (hfc : fc' ≤ T + 1) (hz : CertZip μ env fc' d a b)
    (hI₁ : SubjInv d a) (hI₂ : SubjInv d b) :
    ThetaRelD μ env T d a b :=
  ThetaRelD.zipCore (Γ := []) (sp₁ := []) (sp₂ := [])
    .nil hfc hz hI₁ hI₂ .nil

/-- Prop wrapper. -/
theorem ThetaRel.ofZip {T d fc' : Nat} {a b : Expr}
    (hfc : fc' ≤ T + 1) (hz : CertZip μ env fc' d a b)
    (hI₁ : SubjInv d a) (hI₂ : SubjInv d b) :
    ThetaRel μ env T d a b :=
  ⟨ThetaRelD.ofZip hfc hz hI₁ hI₂⟩

/-- Bounded images under a Θ telescope (LEFT). -/
theorem thetaRel_bounded₁ {T : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat} {X : Expr},
      TelescopeRelD μ env T d Γ →
      X.looseBVarsBounded 0 = true →
      (thetaSubst₁ d Γ X).looseBVarsBounded 0 = true
  | [], _, _ => fun _ hb => hb
  | t :: Γ', d, X => fun hΓ hb => by
    cases hΓ with
    | cons hz hd hI₁ hI₂ hp hΓ' =>
      exact substAK_bounded hI₁.2.1 (thetaRel_bounded₁ hΓ' hb)

/-- Bounded images under a Θ telescope (RIGHT). -/
theorem thetaRel_bounded₂ {T : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat} {X : Expr},
      TelescopeRelD μ env T d Γ →
      X.looseBVarsBounded 0 = true →
      (thetaSubst₂ d Γ X).looseBVarsBounded 0 = true
  | [], _, _ => fun _ hb => hb
  | t :: Γ', d, X => fun hΓ hb => by
    cases hΓ with
    | cons hz hd hI₁ hI₂ hp hΓ' =>
      exact substAK_bounded hI₂.2.1 (thetaRel_bounded₂ hΓ' hb)

/-- Scoped images under a Θ telescope (LEFT). -/
theorem thetaRel_WScoped₁ {T : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat} {X : Expr},
      TelescopeRelD μ env T d Γ →
      Expr.WScoped (d + Γ.length) X →
      Expr.WScoped d (thetaSubst₁ d Γ X)
  | [], _, _ => fun _ hw => hw
  | t :: Γ', d, X => fun hΓ hw => by
    cases hΓ with
    | cons hz hd hI₁ hI₂ hp hΓ' =>
      refine substAK_WScoped hI₁.1 ?_
      refine thetaRel_WScoped₁ hΓ' ?_
      have heq : (d + 1) + Γ'.length = d + (t :: Γ').length := by
        simp [List.length_cons]
        omega
      rw [heq]
      exact hw

/-- Scoped images under a Θ telescope (RIGHT). -/
theorem thetaRel_WScoped₂ {T : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat} {X : Expr},
      TelescopeRelD μ env T d Γ →
      Expr.WScoped (d + Γ.length) X →
      Expr.WScoped d (thetaSubst₂ d Γ X)
  | [], _, _ => fun _ hw => hw
  | t :: Γ', d, X => fun hΓ hw => by
    cases hΓ with
    | cons hz hd hI₁ hI₂ hp hΓ' =>
      refine substAK_WScoped hI₂.1 ?_
      refine thetaRel_WScoped₂ hΓ' ?_
      have heq : (d + 1) + Γ'.length = d + (t :: Γ').length := by
        simp [List.length_cons]
        omega
      rw [heq]
      exact hw

/-- The λ-image's shape and β composite over a Θ telescope
(LEFT). -/
theorem thetaRel_lam_beta₁ {T : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat} {n : Name} {ty b : Expr}
      {m : Setlec.BinderMeta},
      TelescopeRelD μ env T d Γ →
      ∃ TY B, thetaSubst₁ d Γ (.lam n ty b m) = .lam n TY B m ∧
        ∀ x, x.looseBVarsBounded 0 = true →
          B.instantiate1 (thetaSubst₁ d Γ x)
            = thetaSubst₁ d Γ (b.instantiate1 x)
  | [], d, n, ty, b, m => fun _ => ⟨ty, b, rfl, fun x hx => rfl⟩
  | t :: Γ', d, n, ty, b, m => fun hΓ => by
    cases hΓ with
    | cons hz hd hI₁ hI₂ hp hΓ' =>
    obtain ⟨TY', B', hshape, hbeta⟩ :=
      thetaRel_lam_beta₁ (Γ := Γ') (d := d + 1) (n := n)
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
        (thetaRel_bounded₁ hΓ' hx) B' 0, hbeta x hx]
      rfl

/-- The λ-image's shape and β composite over a Θ telescope
(RIGHT). -/
theorem thetaRel_lam_beta₂ {T : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat} {n : Name} {ty b : Expr}
      {m : Setlec.BinderMeta},
      TelescopeRelD μ env T d Γ →
      ∃ TY B, thetaSubst₂ d Γ (.lam n ty b m) = .lam n TY B m ∧
        ∀ x, x.looseBVarsBounded 0 = true →
          B.instantiate1 (thetaSubst₂ d Γ x)
            = thetaSubst₂ d Γ (b.instantiate1 x)
  | [], d, n, ty, b, m => fun _ => ⟨ty, b, rfl, fun x hx => rfl⟩
  | t :: Γ', d, n, ty, b, m => fun hΓ => by
    cases hΓ with
    | cons hz hd hI₁ hI₂ hp hΓ' =>
    obtain ⟨TY', B', hshape, hbeta⟩ :=
      thetaRel_lam_beta₂ (Γ := Γ') (d := d + 1) (n := n)
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
        (thetaRel_bounded₂ hΓ' hx) B' 0, hbeta x hx]
      rfl

/-- The letE-image's shape and zeta composite over a Θ telescope
(LEFT): the image's zeta-contractum is the contractum's image. -/
theorem thetaRel_letE_zeta₁ {T : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat} {n : Name} {ty v b : Expr},
      TelescopeRelD μ env T d Γ →
      v.looseBVarsBounded 0 = true →
      ∃ TY B, thetaSubst₁ d Γ (.letE n ty v b)
          = .letE n TY (thetaSubst₁ d Γ v) B ∧
        B.instantiate1 (thetaSubst₁ d Γ v)
          = thetaSubst₁ d Γ (b.instantiate1 v)
  | [], d, n, ty, v, b => fun _ _ => ⟨ty, b, rfl, rfl⟩
  | t :: Γ', d, n, ty, v, b => fun hΓ hvb => by
    cases hΓ with
    | cons hz hd hI₁ hI₂ hp hΓ' =>
    obtain ⟨TY', B', hshape, hzeta⟩ :=
      thetaRel_letE_zeta₁ (Γ := Γ') (d := d + 1) (n := n)
        (ty := ty) (v := v) (b := b) hΓ' hvb
    refine ⟨substAK d 0 t.a₁ TY', substAK d 1 t.a₁ B', ?_, ?_⟩
    · show substAK d 0 t.a₁
        (thetaSubst₁ (d + 1) Γ' (.letE n ty v b)) = _
      rw [hshape]
      rfl
    · show (substAK d 1 t.a₁ B').instantiate1
        (substAK d 0 t.a₁ (thetaSubst₁ (d + 1) Γ' v)) = _
      rw [substAK_instantiate1 hI₁.2.1
        (thetaRel_bounded₁ hΓ' hvb) B' 0, hzeta]
      rfl

/-- RIGHT-side version. -/
theorem thetaRel_letE_zeta₂ {T : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat} {n : Name} {ty v b : Expr},
      TelescopeRelD μ env T d Γ →
      v.looseBVarsBounded 0 = true →
      ∃ TY B, thetaSubst₂ d Γ (.letE n ty v b)
          = .letE n TY (thetaSubst₂ d Γ v) B ∧
        B.instantiate1 (thetaSubst₂ d Γ v)
          = thetaSubst₂ d Γ (b.instantiate1 v)
  | [], d, n, ty, v, b => fun _ _ => ⟨ty, b, rfl, rfl⟩
  | t :: Γ', d, n, ty, v, b => fun hΓ hvb => by
    cases hΓ with
    | cons hz hd hI₁ hI₂ hp hΓ' =>
    obtain ⟨TY', B', hshape, hzeta⟩ :=
      thetaRel_letE_zeta₂ (Γ := Γ') (d := d + 1) (n := n)
        (ty := ty) (v := v) (b := b) hΓ' hvb
    refine ⟨substAK d 0 t.a₂ TY', substAK d 1 t.a₂ B', ?_, ?_⟩
    · show substAK d 0 t.a₂
        (thetaSubst₂ (d + 1) Γ' (.letE n ty v b)) = _
      rw [hshape]
      rfl
    · show (substAK d 1 t.a₂ B').instantiate1
        (substAK d 0 t.a₂ (thetaSubst₂ (d + 1) Γ' v)) = _
      rw [substAK_instantiate1 hI₂.2.1
        (thetaRel_bounded₂ hΓ' hvb) B' 0, hzeta]
      rfl

/-- The Θ telescope extends (the push's entry). -/
def TelescopeRelD.append {T : Nat} {t : ThetaEntry} :
    ∀ {Γ : List ThetaEntry} {d : Nat},
      TelescopeRelD μ env T d Γ →
      ThetaRelD μ env T (d + Γ.length) t.a₁ t.a₂ →
      ThetaRelD μ env T (d + Γ.length) t.ty₁ t.ty₂ →
      SubjInv (d + Γ.length) t.a₁ →
      SubjInv (d + Γ.length) t.a₂ →
      PairedLeaves t.a₁ t.a₂ →
      TelescopeRelD μ env T d (Γ ++ [t])
  | [], d => fun _ hz hd hI₁ hI₂ hp =>
    .cons hz hd hI₁ hI₂ hp .nil
  | t' :: Γ', d => fun hΓ hz hd hI₁ hI₂ hp => by
    cases hΓ with
    | cons hz' hd' hI₁' hI₂' hp' hΓ'' =>
      have heq : (d + 1) + Γ'.length = d + (Γ'.length + 1) := by
        omega
      exact .cons hz' hd' hI₁' hI₂' hp'
        (TelescopeRelD.append hΓ'' (heq ▸ hz) (heq ▸ hd)
          (heq ▸ hI₁) (heq ▸ hI₂) hp)

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
  (∃ w₁ w₂ c₁ c₂ G₁ G₂, c₁ ≤ g₁ ∧ c₂ ≤ g₂ ∧
    whnfCore μ env c₁ d w₁ = .ok u' ∧
    whnfCore μ env c₂ d w₂ = .ok v' ∧
    RawReach μ env d G₁ u w₁ ∧ RawReach μ env d G₂ v w₂ ∧
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
theorem thetaSubst₁_push {Γ : List ThetaEntry} {d : Nat}
    {b B x : Expr}
    {t : ThetaEntry}
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

/-- The λ-image's shape (LEFT). -/
theorem thetaSubst₁_lam {d : Nat} {n : Name} {ty b : Expr}
    {m : Setlec.BinderMeta} :
    ∀ {Γ : List ThetaEntry},
      ∃ TY B, thetaSubst₁ d Γ (.lam n ty b m)
        = .lam n TY B m
  | [] => ⟨ty, b, rfl⟩
  | t :: Γ' => by
    obtain ⟨TY', B', hs⟩ := thetaSubst₁_lam (Γ := Γ')
      (d := d + 1) (n := n) (ty := ty) (b := b) (m := m)
    refine ⟨substAK d 0 t.a₁ TY', substAK d 1 t.a₁ B', ?_⟩
    show substAK d 0 t.a₁
      (thetaSubst₁ (d + 1) Γ' (.lam n ty b m)) = _
    rw [hs]
    rfl

/-- The λ-image's shape (RIGHT). -/
theorem thetaSubst₂_lam {d : Nat} {n : Name} {ty b : Expr}
    {m : Setlec.BinderMeta} :
    ∀ {Γ : List ThetaEntry},
      ∃ TY B, thetaSubst₂ d Γ (.lam n ty b m)
        = .lam n TY B m
  | [] => ⟨ty, b, rfl⟩
  | t :: Γ' => by
    obtain ⟨TY', B', hs⟩ := thetaSubst₂_lam (Γ := Γ')
      (d := d + 1) (n := n) (ty := ty) (b := b) (m := m)
    refine ⟨substAK d 0 t.a₂ TY', substAK d 1 t.a₂ B', ?_⟩
    show substAK d 0 t.a₂
      (thetaSubst₂ (d + 1) Γ' (.lam n ty b m)) = _
    rw [hs]
    rfl

/-- The letE-image's shape (LEFT). -/
theorem thetaSubst₁_letE {d : Nat} {n : Name} {ty v b : Expr} :
    ∀ {Γ : List ThetaEntry},
      ∃ TY V B, thetaSubst₁ d Γ (.letE n ty v b)
        = .letE n TY V B
  | [] => ⟨ty, v, b, rfl⟩
  | t :: Γ' => by
    obtain ⟨TY', V', B', hs⟩ := thetaSubst₁_letE (Γ := Γ')
      (d := d + 1) (n := n) (ty := ty) (v := v) (b := b)
    refine ⟨substAK d 0 t.a₁ TY', substAK d 0 t.a₁ V',
      substAK d 1 t.a₁ B', ?_⟩
    show substAK d 0 t.a₁
      (thetaSubst₁ (d + 1) Γ' (.letE n ty v b)) = _
    rw [hs]
    rfl

/-- The letE-image's shape (RIGHT). -/
theorem thetaSubst₂_letE {d : Nat} {n : Name} {ty v b : Expr} :
    ∀ {Γ : List ThetaEntry},
      ∃ TY V B, thetaSubst₂ d Γ (.letE n ty v b)
        = .letE n TY V B
  | [] => ⟨ty, v, b, rfl⟩
  | t :: Γ' => by
    obtain ⟨TY', V', B', hs⟩ := thetaSubst₂_letE (Γ := Γ')
      (d := d + 1) (n := n) (ty := ty) (v := v) (b := b)
    refine ⟨substAK d 0 t.a₂ TY', substAK d 0 t.a₂ V',
      substAK d 1 t.a₂ B', ?_⟩
    show substAK d 0 t.a₂
      (thetaSubst₂ (d + 1) Γ' (.letE n ty v b)) = _
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

/-- Below-zone `fvar`s are θ-invariant (neither `abstract1` at a
higher index nor `instantiate1` touches an `fvar` node). -/
theorem thetaSubst₁_fvar_below :
    ∀ {Γ : List ThetaEntry} {d j : Nat} {n : Name} {ty : Expr},
      j < d →
      thetaSubst₁ d Γ (.fvar j n ty) = .fvar j n ty
  | [], _, _, _, _ => fun _ => rfl
  | t :: Γ', d, j, n, ty => fun hj => by
    show substAK d 0 t.a₁ (thetaSubst₁ (d + 1) Γ' (.fvar j n ty))
      = _
    rw [thetaSubst₁_fvar_below (Γ := Γ') (by omega : j < d + 1)]
    unfold substAK
    simp only [Setlec.Expr.abstract1]
    rw [if_neg (by omega : j ≠ d)]
    rfl

/-- RIGHT-side version. -/
theorem thetaSubst₂_fvar_below :
    ∀ {Γ : List ThetaEntry} {d j : Nat} {n : Name} {ty : Expr},
      j < d →
      thetaSubst₂ d Γ (.fvar j n ty) = .fvar j n ty
  | [], _, _, _, _ => fun _ => rfl
  | t :: Γ', d, j, n, ty => fun hj => by
    show substAK d 0 t.a₂ (thetaSubst₂ (d + 1) Γ' (.fvar j n ty))
      = _
    rw [thetaSubst₂_fvar_below (Γ := Γ') (by omega : j < d + 1)]
    unfold substAK
    simp only [Setlec.Expr.abstract1]
    rw [if_neg (by omega : j ≠ d)]
    rfl

/-- In-zone `fvar`s resolve to the entry's argument under the
PREFIX telescope (LEFT). -/
theorem thetaSubst₁_fvar_inzone :
    ∀ {Γ : List ThetaEntry} {d k : Nat} {n : Name} {ty : Expr}
      (hk : k < Γ.length),
      thetaSubst₁ d Γ (.fvar (d + k) n ty)
        = thetaSubst₁ d (Γ.take k) Γ[k].a₁
  | [], _, k, _, _ => fun hk => absurd hk (by simp)
  | t :: Γ', d, 0, n, ty => fun hk => by
    show substAK d 0 t.a₁
      (thetaSubst₁ (d + 1) Γ' (.fvar (d + 0) n ty)) = _
    rw [thetaSubst₁_fvar_below (Γ := Γ')
      (by omega : d + 0 < d + 1)]
    show ((Expr.fvar (d + 0) n ty).abstract1 d 0).instantiate1
      t.a₁ 0 = _
    simp only [Setlec.Expr.abstract1]
    rw [if_pos (by omega : d + 0 = d)]
    rfl
  | t :: Γ', d, (k' + 1), n, ty => fun hk => by
    show substAK d 0 t.a₁
      (thetaSubst₁ (d + 1) Γ' (.fvar (d + (k' + 1)) n ty)) = _
    have heq : d + (k' + 1) = (d + 1) + k' := by omega
    rw [heq, thetaSubst₁_fvar_inzone (Γ := Γ') (d := d + 1)
      (by simpa using Nat.lt_of_succ_lt_succ hk)]
    rfl

/-- RIGHT-side version. -/
theorem thetaSubst₂_fvar_inzone :
    ∀ {Γ : List ThetaEntry} {d k : Nat} {n : Name} {ty : Expr}
      (hk : k < Γ.length),
      thetaSubst₂ d Γ (.fvar (d + k) n ty)
        = thetaSubst₂ d (Γ.take k) Γ[k].a₂
  | [], _, k, _, _ => fun hk => absurd hk (by simp)
  | t :: Γ', d, 0, n, ty => fun hk => by
    show substAK d 0 t.a₂
      (thetaSubst₂ (d + 1) Γ' (.fvar (d + 0) n ty)) = _
    rw [thetaSubst₂_fvar_below (Γ := Γ')
      (by omega : d + 0 < d + 1)]
    show ((Expr.fvar (d + 0) n ty).abstract1 d 0).instantiate1
      t.a₂ 0 = _
    simp only [Setlec.Expr.abstract1]
    rw [if_pos (by omega : d + 0 = d)]
    rfl
  | t :: Γ', d, (k' + 1), n, ty => fun hk => by
    show substAK d 0 t.a₂
      (thetaSubst₂ (d + 1) Γ' (.fvar (d + (k' + 1)) n ty)) = _
    have heq : d + (k' + 1) = (d + 1) + k' := by omega
    rw [heq, thetaSubst₂_fvar_inzone (Γ := Γ') (d := d + 1)
      (by simpa using Nat.lt_of_succ_lt_succ hk)]
    rfl

/-- Telescope images compose over concatenation (LEFT). -/
theorem thetaSubst₁_concat :
    ∀ {Γ₁ Γ₂ : List ThetaEntry} {d : Nat} {e : Expr},
      thetaSubst₁ d (Γ₁ ++ Γ₂) e
        = thetaSubst₁ d Γ₁ (thetaSubst₁ (d + Γ₁.length) Γ₂ e)
  | [], Γ₂, d, e => by
    show thetaSubst₁ d Γ₂ e = thetaSubst₁ (d + 0) Γ₂ e
    rfl
  | t :: Γ₁', Γ₂, d, e => by
    show substAK d 0 t.a₁ (thetaSubst₁ (d + 1) (Γ₁' ++ Γ₂) e) = _
    rw [thetaSubst₁_concat (Γ₁ := Γ₁')]
    have heq : (d + 1) + Γ₁'.length = d + (Γ₁'.length + 1) := by
      omega
    rw [heq]
    rfl

/-- Telescope images compose over concatenation (RIGHT). -/
theorem thetaSubst₂_concat :
    ∀ {Γ₁ Γ₂ : List ThetaEntry} {d : Nat} {e : Expr},
      thetaSubst₂ d (Γ₁ ++ Γ₂) e
        = thetaSubst₂ d Γ₁ (thetaSubst₂ (d + Γ₁.length) Γ₂ e)
  | [], Γ₂, d, e => by
    show thetaSubst₂ d Γ₂ e = thetaSubst₂ (d + 0) Γ₂ e
    rfl
  | t :: Γ₁', Γ₂, d, e => by
    show substAK d 0 t.a₂ (thetaSubst₂ (d + 1) (Γ₁' ++ Γ₂) e) = _
    rw [thetaSubst₂_concat (Γ₁ := Γ₁')]
    have heq : (d + 1) + Γ₁'.length = d + (Γ₁'.length + 1) := by
      omega
    rw [heq]
    rfl

/-- Telescope depth reindexing, named for size lemmas. -/
def TelescopeRelD.castD {T d₁ d₂ : Nat} {Γ : List ThetaEntry}
    (heq : d₁ = d₂) (x : TelescopeRelD μ env T d₁ Γ) :
    TelescopeRelD μ env T d₂ Γ := heq ▸ x

/-- Depth reindexing along an equation, as a named function so
size lemmas can target it. -/
def ThetaRelD.castD {T d₁ d₂ : Nat} {u v : Expr}
    (heq : d₁ = d₂) (x : ThetaRelD μ env T d₁ u v) :
    ThetaRelD μ env T d₂ u v := heq ▸ x

/-- Telescopes concatenate. -/
def TelescopeRelD.concat {T : Nat} :
    ∀ {Γ₁ Γ₂ : List ThetaEntry} {d : Nat},
      TelescopeRelD μ env T d Γ₁ →
      TelescopeRelD μ env T (d + Γ₁.length) Γ₂ →
      TelescopeRelD μ env T d (Γ₁ ++ Γ₂)
  | [], _, _ => fun _ h₂ => h₂
  | t :: Γ₁', Γ₂, d => fun h₁ h₂ =>
    match h₁ with
    | .cons hz hd hI₁ hI₂ hp hΓ' =>
      .cons hz hd hI₁ hI₂ hp
        (TelescopeRelD.concat hΓ'
          (h₂.castD (by simp only [List.length_cons]; omega)))

/-- Head congruence lifts a trace through a spine. -/
theorem RawReach.mkAppN_left {d G : Nat} {f f' : Expr} :
    ∀ (as : List Expr),
      RawReach μ env d G f f' →
      RawReach μ env d G (Setlec.Expr.mkAppN f as)
        (Setlec.Expr.mkAppN f' as)
  | [], h => h
  | a :: as, h => by
    show RawReach μ env d G
      (Setlec.Expr.mkAppN (.app f a) as)
      (Setlec.Expr.mkAppN (.app f' a) as)
    exact RawReach.mkAppN_left as (.appL a h (.refl _))

/-- Row weight (the syn-hop's slot: zip rows delegate to run rows
delegate to same rows). -/
def ThetaRelD.rowW {T d : Nat} {u v : Expr} :
    ThetaRelD μ env T d u v → Nat
  | .zipCore _ _ _ _ _ _ => 2
  | .runCore _ _ _ _ _ _ => 1
  | .sameCore _ _ _ => 0

/-- The run row's remaining defeq budget (the δ/nat re-entries'
slot). -/
def ThetaRelD.rowL {T d : Nat} {u v : Expr} :
    ThetaRelD μ env T d u v → Nat
  | .runCore (L := L) _ _ _ _ _ _ => L
  | _ => 0

/-- Prefix of a Θ telescope, as data. -/
def TelescopeRelD.takeD {T : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat},
      TelescopeRelD μ env T d Γ → ∀ (k : Nat),
      TelescopeRelD μ env T d (Γ.take k)
  | _, _, _, 0 => .nil
  | [], _, _, (_ + 1) => .nil
  | _ :: _, _, .cons hz hd hI₁ hI₂ hp rest, (k + 1) =>
    .cons hz hd hI₁ hI₂ hp (rest.takeD k)

/-- The `k`-th entry's argument relation. -/
def TelescopeRelD.lookup {T : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat},
      TelescopeRelD μ env T d Γ → ∀ (k : Nat)
      (hk : k < Γ.length),
      ThetaRelD μ env T (d + k) (Γ[k]'hk).a₁ (Γ[k]'hk).a₂
  | _ :: _, _, .cons hz hd hI₁ hI₂ hp rest, 0, _ => hz
  | _ :: Γ', d, .cons hz hd hI₁ hI₂ hp rest, (k + 1), hk => by
    have hk' : k < Γ'.length := by simpa using hk
    have h := TelescopeRelD.lookup rest k hk'
    have heq : d + 1 + k = d + (k + 1) := by omega
    exact h.castD heq

/-- Subject reindexing along expression equations. -/
def ThetaRelD.castE {T d : Nat} {u u' v v' : Expr}
    (hu : u = u') (hv : v = v')
    (x : ThetaRelD μ env T d u v) :
    ThetaRelD μ env T d u' v' := hu ▸ hv ▸ x

mutual
/-- **The discharge weight**: node counts only — no type-index
terms, so concatenation is exactly additive. -/
def ThetaRelD.wt {T d : Nat} {u v : Expr} :
    ThetaRelD μ env T d u v → Nat
  | .zipCore hT _ _ _ _ hsp => 1 + hT.wt + hsp.wt
  | .runCore hT _ _ _ _ hsp => 1 + hT.wt + hsp.wt
  | .sameCore hT _ hsp => 1 + hT.wt + hsp.wt

/-- Spine weight. -/
def ThetaRelsD.wt {T d : Nat} {as bs : List Expr} :
    ThetaRelsD μ env T d as bs → Nat
  | .nil => 1
  | .cons h rest => 1 + h.wt + rest.wt

/-- Telescope weight. -/
def TelescopeRelD.wt {T d : Nat} {Γ : List ThetaEntry} :
    TelescopeRelD μ env T d Γ → Nat
  | .nil => 1
  | .cons hz hd _ _ _ rest => 1 + hz.wt + hd.wt + rest.wt
end

@[simp] theorem ThetaRelD.wt_zipCore {T d : Nat}
    {Γ : List ThetaEntry} {fc' : Nat} {A₁ A₂ : Expr}
    {sp₁ sp₂ : List Expr} (hT : TelescopeRelD μ env T d Γ)
    (hfc : fc' ≤ T + 1)
    (hz : CertZip μ env fc' (d + Γ.length) A₁ A₂)
    (hC₁ : SubjInv (d + Γ.length) A₁)
    (hC₂ : SubjInv (d + Γ.length) A₂)
    (hsp : ThetaRelsD μ env T d sp₁ sp₂) :
    (ThetaRelD.zipCore hT hfc hz hC₁ hC₂ hsp).wt
      = 1 + hT.wt + hsp.wt := rfl

@[simp] theorem ThetaRelD.wt_runCore {T d : Nat}
    {Γ : List ThetaEntry} {k L : Nat} {C₁ C₂ : Expr}
    {sp₁ sp₂ : List Expr} (hT : TelescopeRelD μ env T d Γ)
    (hk : k ≤ T)
    (hrun : Setlec.defeqLoop μ (Setlec.pureFns μ env k) env
      (d + Γ.length) L C₁ C₂ = .ok true)
    (hC₁ : SubjInv (d + Γ.length) C₁)
    (hC₂ : SubjInv (d + Γ.length) C₂)
    (hsp : ThetaRelsD μ env T d sp₁ sp₂) :
    (ThetaRelD.runCore hT hk hrun hC₁ hC₂ hsp).wt
      = 1 + hT.wt + hsp.wt := rfl

@[simp] theorem ThetaRelD.wt_sameCore {T d : Nat}
    {Γ : List ThetaEntry} {P : Expr} {sp₁ sp₂ : List Expr}
    (hT : TelescopeRelD μ env T d Γ)
    (hP : SubjInv (d + Γ.length) P)
    (hsp : ThetaRelsD μ env T d sp₁ sp₂) :
    (ThetaRelD.sameCore hT hP hsp).wt = 1 + hT.wt + hsp.wt := rfl

@[simp] theorem ThetaRelsD.wt_nil {T d : Nat} :
    (ThetaRelsD.nil (μ := μ) (env := env) (T := T) (d := d)).wt
      = 1 := rfl

@[simp] theorem ThetaRelsD.wt_cons {T d : Nat} {a b : Expr}
    {as bs : List Expr} (h : ThetaRelD μ env T d a b)
    (rest : ThetaRelsD μ env T d as bs) :
    (ThetaRelsD.cons h rest).wt = 1 + h.wt + rest.wt := rfl

@[simp] theorem TelescopeRelD.wt_nil {T d : Nat} :
    (TelescopeRelD.nil (μ := μ) (env := env) (T := T) (d := d)).wt
      = 1 := rfl

@[simp] theorem TelescopeRelD.wt_cons {T d : Nat}
    {t : ThetaEntry} {Γ : List ThetaEntry}
    (hz : ThetaRelD μ env T d t.a₁ t.a₂)
    (hd : ThetaRelD μ env T d t.ty₁ t.ty₂)
    (hI₁ : SubjInv d t.a₁) (hI₂ : SubjInv d t.a₂)
    (hp : PairedLeaves t.a₁ t.a₂)
    (rest : TelescopeRelD μ env T (d + 1) Γ) :
    (TelescopeRelD.cons hz hd hI₁ hI₂ hp rest).wt
      = 1 + hz.wt + hd.wt + rest.wt := rfl

theorem ThetaRelD.wt_pos {T d : Nat} {u v : Expr}
    (h : ThetaRelD μ env T d u v) : 0 < h.wt := by
  cases h <;> simp [ThetaRelD.wt] <;> omega

theorem ThetaRelsD.wt_pos {T d : Nat} {as bs : List Expr}
    (h : ThetaRelsD μ env T d as bs) : 0 < h.wt := by
  cases h <;> simp [ThetaRelsD.wt] <;> omega

theorem TelescopeRelD.wt_pos {T d : Nat} {Γ : List ThetaEntry}
    (h : TelescopeRelD μ env T d Γ) : 0 < h.wt := by
  cases h <;> simp [TelescopeRelD.wt] <;> omega

@[simp] theorem TelescopeRelD.wt_castD {T d₁ d₂ : Nat}
    {Γ : List ThetaEntry} (heq : d₁ = d₂)
    (x : TelescopeRelD μ env T d₁ Γ) :
    (x.castD heq).wt = x.wt := by
  subst heq
  rfl

@[simp] theorem ThetaRelD.wt_castD {T d₁ d₂ : Nat} {u v : Expr}
    (heq : d₁ = d₂) (x : ThetaRelD μ env T d₁ u v) :
    (x.castD heq).wt = x.wt := by
  subst heq
  rfl

@[simp] theorem ThetaRelD.wt_castE {T d : Nat} {u u' v v' : Expr}
    (hu : u = u') (hv : v = v') (x : ThetaRelD μ env T d u v) :
    (x.castE hu hv).wt = x.wt := by
  subst hu
  subst hv
  rfl

/-- Spine depth reindexing. -/
def ThetaRelsD.castD {T d₁ d₂ : Nat} {as bs : List Expr}
    (heq : d₁ = d₂) (x : ThetaRelsD μ env T d₁ as bs) :
    ThetaRelsD μ env T d₂ as bs := heq ▸ x

@[simp] theorem ThetaRelsD.wt_castD {T d₁ d₂ : Nat}
    {as bs : List Expr} (heq : d₁ = d₂)
    (x : ThetaRelsD μ env T d₁ as bs) :
    (x.castD heq).wt = x.wt := by
  subst heq
  rfl

/-- The prefix never outweighs the telescope. -/
theorem TelescopeRelD.wt_takeD {T : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat}
      (h : TelescopeRelD μ env T d Γ) (k : Nat),
      (h.takeD k).wt ≤ h.wt
  | [], _, .nil, 0 => Nat.le_refl _
  | [], _, .nil, (_ + 1) => Nat.le_refl _
  | _ :: _, _, .cons hz hd hI₁ hI₂ hp rest, 0 => by
    have e1 : ((TelescopeRelD.cons hz hd hI₁ hI₂ hp rest).takeD
        0).wt = 1 := rfl
    have e2 : (TelescopeRelD.cons hz hd hI₁ hI₂ hp rest).wt
        = 1 + hz.wt + hd.wt + rest.wt := rfl
    have h4 := rest.wt_pos
    omega
  | _ :: _, _, .cons hz hd hI₁ hI₂ hp rest, (k + 1) => by
    have ih := TelescopeRelD.wt_takeD rest k
    have e1 : ((TelescopeRelD.cons hz hd hI₁ hI₂ hp rest).takeD
        (k + 1)).wt
        = 1 + hz.wt + hd.wt + (rest.takeD k).wt := rfl
    have e2 : (TelescopeRelD.cons hz hd hI₁ hI₂ hp rest).wt
        = 1 + hz.wt + hd.wt + rest.wt := rfl
    omega

/-- The looked-up entry plus the prefix stay strictly inside. -/
theorem TelescopeRelD.wt_lookup {T : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat}
      (h : TelescopeRelD μ env T d Γ) (k : Nat)
      (hk : k < Γ.length),
      (h.lookup k hk).wt + (h.takeD k).wt < h.wt
  | _ :: _, _, .cons hz hd hI₁ hI₂ hp rest, 0, hk => by
    have h4 := hd.wt_pos
    have e1 : ((TelescopeRelD.cons hz hd hI₁ hI₂ hp rest).takeD
        0).wt = 1 := rfl
    have e2 : (TelescopeRelD.cons hz hd hI₁ hI₂ hp rest).wt
        = 1 + hz.wt + hd.wt + rest.wt := rfl
    have e3 : ((TelescopeRelD.cons hz hd hI₁ hI₂ hp rest).lookup
        0 hk).wt = hz.wt := rfl
    have h5 := rest.wt_pos
    omega
  | _ :: Γ', d, .cons hz hd hI₁ hI₂ hp rest, (k + 1), hk => by
    have hk' : k < Γ'.length := by simpa using hk
    have ih := TelescopeRelD.wt_lookup rest k hk'
    have heq : d + 1 + k = d + (k + 1) := by omega
    have e3 : ((TelescopeRelD.cons hz hd hI₁ hI₂ hp rest).lookup
        (k + 1) hk).wt = ((rest.lookup k hk').castD heq).wt := rfl
    have hcast := ThetaRelD.wt_castD heq (rest.lookup k hk')
    have e1 : ((TelescopeRelD.cons hz hd hI₁ hI₂ hp rest).takeD
        (k + 1)).wt
        = 1 + hz.wt + hd.wt + (rest.takeD k).wt := rfl
    have e2 : (TelescopeRelD.cons hz hd hI₁ hI₂ hp rest).wt
        = 1 + hz.wt + hd.wt + rest.wt := rfl
    omega

/-- Concatenation is exactly one node cheaper than the parts. -/
theorem TelescopeRelD.wt_concat {T : Nat} :
    ∀ {Γ₁ Γ₂ : List ThetaEntry} {d : Nat}
      (h₁ : TelescopeRelD μ env T d Γ₁)
      (h₂ : TelescopeRelD μ env T (d + Γ₁.length) Γ₂),
      (h₁.concat h₂).wt ≤ h₁.wt + h₂.wt
  | [], _, _, .nil, h₂ => by
    show h₂.wt ≤ _
    exact Nat.le_add_left _ _
  | t :: Γ₁', Γ₂, d, .cons hz hd hI₁ hI₂ hp hΓ', h₂ => by
    have heq : d + (t :: Γ₁').length = (d + 1) + Γ₁'.length := by
      simp only [List.length_cons]; omega
    have ih := TelescopeRelD.wt_concat hΓ' (h₂.castD heq)
    have h1 : ((TelescopeRelD.cons hz hd hI₁ hI₂ hp hΓ').concat
        h₂).wt = 1 + hz.wt + hd.wt
          + (hΓ'.concat (h₂.castD heq)).wt := rfl
    have h4 := TelescopeRelD.wt_castD heq h₂
    have e2 : (TelescopeRelD.cons hz hd hI₁ hI₂ hp hΓ').wt
        = 1 + hz.wt + hd.wt + hΓ'.wt := rfl
    omega

mutual
/-- **Image composition**: a relation at the inner depth, viewed
through an outer Θ telescope, is a relation on the images (the
rows compose by telescope concatenation). Construction only — the
result's size is unconstrained. -/
def ThetaRelD.underTele {T : Nat} {d : Nat} {Γo : List ThetaEntry}
    (hΓo : TelescopeRelD μ env T d Γo) :
    ∀ {uu vv : Expr},
      ThetaRelD μ env T (d + Γo.length) uu vv →
      ThetaRelD μ env T d (thetaSubst₁ d Γo uu)
        (thetaSubst₂ d Γo vv)
  | _, _, .zipCore (Γ := Γe) (A₁ := A₁) (A₂ := A₂) (sp₁ := sp₁)
      (sp₂ := sp₂) hT hfc hz hC₁ hC₂ hsp =>
    have hlen : d + Γo.length + Γe.length
        = d + (Γo ++ Γe).length := by
      simp only [List.length_append]; omega
    ThetaRelD.castE
      (by rw [thetaSubst₁_mkAppN, thetaSubst₁_concat])
      (by rw [thetaSubst₂_mkAppN, thetaSubst₂_concat])
      (ThetaRelD.zipCore (hΓo.concat hT) hfc (hlen ▸ hz)
        (hlen ▸ hC₁) (hlen ▸ hC₂) (hΓo.imageRels hsp))
  | _, _, .runCore (Γ := Γe) (C₁ := C₁) (C₂ := C₂) (sp₁ := sp₁)
      (sp₂ := sp₂) hT hk hrun hC₁ hC₂ hsp =>
    have hlen : d + Γo.length + Γe.length
        = d + (Γo ++ Γe).length := by
      simp only [List.length_append]; omega
    ThetaRelD.castE
      (by rw [thetaSubst₁_mkAppN, thetaSubst₁_concat])
      (by rw [thetaSubst₂_mkAppN, thetaSubst₂_concat])
      (ThetaRelD.runCore (hΓo.concat hT) hk (hlen ▸ hrun)
        (hlen ▸ hC₁) (hlen ▸ hC₂) (hΓo.imageRels hsp))
  | _, _, .sameCore (Γ := Γe) (P := P) (sp₁ := sp₁) (sp₂ := sp₂)
      hT hP hsp =>
    have hlen : d + Γo.length + Γe.length
        = d + (Γo ++ Γe).length := by
      simp only [List.length_append]; omega
    ThetaRelD.castE
      (by rw [thetaSubst₁_mkAppN, thetaSubst₁_concat])
      (by rw [thetaSubst₂_mkAppN, thetaSubst₂_concat])
      (ThetaRelD.sameCore (hΓo.concat hT) (hlen ▸ hP)
        (hΓo.imageRels hsp))

/-- Spine-wise image composition. -/
def TelescopeRelD.imageRels {T : Nat} {d : Nat}
    {Γo : List ThetaEntry} (hΓo : TelescopeRelD μ env T d Γo) :
    ∀ {as bs : List Expr},
      ThetaRelsD μ env T (d + Γo.length) as bs →
      ThetaRelsD μ env T d (as.map (thetaSubst₁ d Γo))
        (bs.map (thetaSubst₂ d Γo))
  | _, _, .nil => .nil
  | _, _, .cons h rest =>
    .cons (h.underTele (hΓo := hΓo)) (hΓo.imageRels rest)
end

/-- Spines append. -/
def ThetaRelsD.appendR {T d : Nat} :
    ∀ {as bs cs ds : List Expr},
      ThetaRelsD μ env T d as bs → ThetaRelsD μ env T d cs ds →
      ThetaRelsD μ env T d (as ++ cs) (bs ++ ds)
  | [], [], _, _, .nil, h₂ => h₂
  | _ :: _, _ :: _, _, _, .cons h rest, h₂ =>
    .cons h (rest.appendR h₂)

/-- Snoc view of a related spine (peeling the outermost app). -/
inductive RelsSnocView (μ : CheckMode) (env : Env) (T d : Nat) :
    List Expr → List Expr → Type
  | nil : RelsSnocView μ env T d [] []
  | snoc {as bs : List Expr} {a b : Expr}
      (init : ThetaRelsD μ env T d as bs)
      (last : ThetaRelD μ env T d a b) :
      RelsSnocView μ env T d (as ++ [a]) (bs ++ [b])

/-- Every related spine has a snoc view. -/
def ThetaRelsD.snocView {T d : Nat} :
    ∀ {as bs : List Expr}, ThetaRelsD μ env T d as bs →
      RelsSnocView μ env T d as bs
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h rest =>
    match rest.snocView with
    | .nil => .snoc .nil h
    | .snoc init last => .snoc (.cons h init) last

/-- A relation extends across one more (outermost) argument. -/
def ThetaRelD.extendSp {T d : Nat} {u v z₁ z₂ : Expr}
    (hz : ThetaRelD μ env T d z₁ z₂) :
    ThetaRelD μ env T d u v →
    ThetaRelD μ env T d (.app u z₁) (.app v z₂)
  | .zipCore (sp₁ := sp₁) (sp₂ := sp₂) hT hfc hzc hC₁ hC₂ hsp =>
    ThetaRelD.castE
      (by rw [mkAppN_append]; rfl) (by rw [mkAppN_append]; rfl)
      (ThetaRelD.zipCore hT hfc hzc hC₁ hC₂
        (hsp.appendR (.cons hz .nil)))
  | .runCore (sp₁ := sp₁) (sp₂ := sp₂) hT hk hrun hC₁ hC₂ hsp =>
    ThetaRelD.castE
      (by rw [mkAppN_append]; rfl) (by rw [mkAppN_append]; rfl)
      (ThetaRelD.runCore hT hk hrun hC₁ hC₂
        (hsp.appendR (.cons hz .nil)))
  | .sameCore (sp₁ := sp₁) (sp₂ := sp₂) hT hP hsp =>
    ThetaRelD.castE
      (by rw [mkAppN_append]; rfl) (by rw [mkAppN_append]; rfl)
      (ThetaRelD.sameCore hT hP
        (hsp.appendR (.cons hz .nil)))

end Discharge

end Setlec.SetR.Interp2
