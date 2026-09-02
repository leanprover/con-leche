import Setlec.SetR.Interp2.BasisQuotP

/-!
# The `Eq` block, P tier (task #161, ENDGAME H)

The one block the layer does not carry: there is no `BConst` for `Eq`,
so nothing here goes through `BConst.type2`/`BitAgree`/`bval2_mem_type`
— every type reading's grading and membership is discharged against
the block's **own** towers (`Interp2/EqTowerP.lean`), which is exactly
why the ENDGAME E seal built them first.

Two structural consequences:

* the `Eq` cons is the tier's one `eq_lawP`-bespoke cons
  (`eqLawP_cons_fresh`'s side condition is `eqName ≠ c₀.name`), and it
  is discharged by `eqLawP_of_tower` through
  `declStepPM_of_basis_cons_eqrow`;
* `Eq.rec`'s stored rule returns its **minor premise**, so its fired
  equality is an identity between two collapsed towers rather than a
  value law — and the only real content is that the major premise's
  membership forces `a = b` and the proof to be `pt`.

The three constants' bits are forced, not chosen (ENDGAME E §1):
`Eq`'s three binders are `.never`, `Eq.refl`'s two are
`.ifAllZero []`, and `Eq.rec`'s six are `.ifAllZero [u_1]`.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr EnvS eqValT eqReflValT eqRecValT)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule uN u1N vN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

section Eq

open Setlec (eqA eqReflA eqRecA eqName eqReflName)

variable {m : EnvS2Core V env} {A : (Name → Nat) → AVExpr}

/-! ## The two spines the block's types are built from -/

/-- `@Eq.{u} α a b`, read through the tower. -/
def eqSpineP (ψ : Name → Nat) (i j k : Nat) : AVExpr :=
  .app (.app (.app (eqValT2 ψ) (.bvar i)) (.bvar j)) (.bvar k)

/-- `@Eq.refl.{u} α a`, read through the tower. -/
def eqReflSpineP (ψ : Name → Nat) (i j : Nat) : AVExpr :=
  .app (.app (eqReflValT2 ψ) (.bvar i)) (.bvar j)

theorem eqSpineP_interp {ψ : Name → Nat} {i j k : Nat} {ρ : Nat → V}
    {Aset a b : V} (hi : ρ i = Aset) (hj : ρ j = a) (hk : ρ k = b)
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset) (hb : b ∈ˢ Aset) :
    interp2 V ρ (eqSpineP ψ i j k) = eqv a b ∧
      AnnotOkP V ρ (eqSpineP ψ i j k) ∧
      interp2 V ρ (eqSpineP ψ i j k) ∈ˢ (univZero : V) := by
  have hAi : interp2 V ρ (AVExpr.bvar i) = Aset := by
    rw [interp2_bvar, hi]
  have haj : interp2 V ρ (AVExpr.bvar j) = a := by
    rw [interp2_bvar, hj]
  have hbk : interp2 V ρ (AVExpr.bvar k) = b := by
    rw [interp2_bvar, hk]
  obtain ⟨hok, hz⟩ := eqValT2_app₃_okP ψ ρ (Aa := .bvar i) (la := .bvar j)
    (ra := .bvar k) ⟨trivial, trivial⟩ ⟨trivial, trivial⟩
    ⟨trivial, trivial⟩ (by rw [hAi]; exact hA)
    (by rw [hAi, haj]; exact ha) (by rw [hAi, hbk]; exact hb)
  refine ⟨?_, hok, hz⟩
  rw [eqSpineP, interp2_app, interp2_app, interp2_app, hAi, haj, hbk,
    eqValT2_app₃ ψ ρ Aset a b hA ha hb]

theorem eqReflSpineP_data {ψ : Name → Nat} {i j : Nat} {ρ : Nat → V}
    {Aset a : V} (hi : ρ i = Aset) (hj : ρ j = a)
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset) :
    interp2 V ρ (eqReflSpineP ψ i j) = (pt : V) ∧
      AnnotOkP V ρ (eqReflSpineP ψ i j) := by
  have hpt : interp2 V ρ (eqReflValT2 ψ) = (pt : V) :=
    eqReflValT2_interp ψ ρ
  have hAi : interp2 V ρ (AVExpr.bvar i) = Aset := by
    rw [interp2_bvar, hi]
  have haj : interp2 V ρ (AVExpr.bvar j) = a := by
    rw [interp2_bvar, hj]
  have h1 := AnnotOkP_app_pt (S := (univ (ψ uN) : V))
    (a := AVExpr.bvar i) (eqReflValT2_okP ψ ρ) hpt
    ⟨trivial, trivial⟩ (by rw [hAi]; exact hA)
  have h2 := AnnotOkP_app_pt (S := Aset) (a := AVExpr.bvar j)
    h1.1 h1.2 ⟨trivial, trivial⟩ (by rw [haj]; exact ha)
  exact ⟨h2.2, h2.1⟩

/-! ## `Eq` and `Eq.refl` -/

/-- `Eq`'s type reading: three graph-regime binders. -/
def eqTyP (ψ : Name → Nat) : AVExpr :=
  .pi 0 1 (.sort (ψ uN)) (.pi 0 1 (.bvar 0) (.pi 0 1 (.bvar 1) (.sort 0)))

/-- `Eq.refl`'s type reading: two squash-regime binders over the
spine. -/
def eqReflTyP (ψ : Name → Nat) : AVExpr :=
  .pi 0 0 (.sort (ψ uN)) (.pi 0 0 (.bvar 0) (eqSpineP ψ 1 0 0))

/-- **`Eq`'s type reading.** -/
theorem denoteP_eqA_type
    {acval : Name → (Name → Nat) → AVExpr} (ψ : Name → Nat) :
    denoteP acval ⟨eqA :: env.consts⟩ ψ 0 eqA.toConstantVal.type
      = some (eqTyP ψ) := by
  simp [eqA, ConstantInfo.toConstantVal, denoteP_forallE, denoteP_sort,
    denoteP_fvar, Expr.instantiate1, eqTyP, pwBit_never, Level.eval, uN]

theorem eqTyP_okP (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOkP V ρ (eqTyP ψ) :=
  ⟨⟨trivial, fun _ _ => ⟨trivial, fun _ _ => ⟨trivial,
      fun _ _ => trivial⟩⟩⟩,
    ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => ⟨trivial,
        fun _ _ => trivial, fun h => absurd h Nat.one_ne_zero⟩,
      fun h => absurd h Nat.one_ne_zero⟩,
    fun h => absurd h Nat.one_ne_zero⟩⟩

theorem eqTyP_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp2 V ρ (eqTyP ψ)
      = piR 1 (univ (ψ uN) : V)
          (fun a => piR 1 a (fun _ => piR 1 a (fun _ => univZero))) := by
  rw [eqTyP, interp2_pi, interp2_sort]
  refine piR_congr fun a _ => ?_
  rw [interp2_pi]
  simp only [interp2_bvar, cons]
  refine piR_congr fun x _ => ?_
  rw [interp2_pi]
  simp only [interp2_bvar, interp2_sort, cons]
  exact piR_congr fun _ _ => univ_zero

/-- **`Eq.refl`'s type reading.**  Stated at *any* extension whose
cons is not `Eq`, because `Eq.rec`'s row reads it as its fired
constructor's telescope. -/
theorem denoteP_eqReflTy {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = eqName)
    (hE : env.find? eqName = some eqA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValT2 ψ) :
    denoteP (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ 0
        eqReflA.toConstantVal.type
      = some (eqReflTyP ψ) := by
  have hEc : ∀ d : Nat,
      denoteP (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const eqName [.param uN]) = some (eqValT2 ψ) := by
    intro d
    rw [denoteP_eqLeaf (m := m) (A := A) ψ (Level.param uN) hne hE d,
      show ([Level.param uN] : List Level)
        = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN], hEv]
  rw [show eqReflA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
            (.app (.app (.app (.const eqName [.param uN]) (.bvar 1))
              (.bvar 0)) (.bvar 0))
            { bi := .default, pw := .ifAllZero [] })
          { bi := .implicit, pw := .ifAllZero [] } from rfl]
  simp [denoteP_forallE, denoteP_sort, denoteP_app, denoteP_fvar,
    Expr.instantiate1, eqReflTyP, eqSpineP, pwBit_ifAllZero_nil, hEc,
    Level.eval]

theorem eqReflTyP_data (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOkP V ρ (eqReflTyP ψ) ∧
      interp2 V ρ (eqReflTyP ψ)
        = piR 0 (univ (ψ uN) : V) (fun a => piR 0 a (fun x => eqv x x)) := by
  have hstep : ∀ Aset x : V, Aset ∈ˢ (univ (ψ uN) : V) → x ∈ˢ Aset →
      interp2 V (cons x (cons Aset ρ)) (eqSpineP ψ 1 0 0) = eqv x x ∧
      AnnotOkP V (cons x (cons Aset ρ)) (eqSpineP ψ 1 0 0) ∧
      interp2 V (cons x (cons Aset ρ)) (eqSpineP ψ 1 0 0)
        ∈ˢ (univZero : V) := by
    intro Aset x hA hx
    exact eqSpineP_interp (ρ := cons x (cons Aset ρ))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA hx hx
  constructor
  · rw [eqReflTyP]
    refine (AnnotOkP_pi_zero (Aa := .sort (ψ uN)) ⟨trivial, trivial⟩
      ?_ ?_).1
    all_goals (
      intro Aset hAset
      rw [interp2_sort] at hAset
      have hlev := AnnotOkP_pi_zero (Aa := AVExpr.bvar 0)
        (ρ := cons Aset ρ) ⟨trivial, trivial⟩
        (fun x hx => (hstep Aset x hAset
          (by simpa [interp2_bvar, cons] using hx)).2.1)
        (fun x hx => (hstep Aset x hAset
          (by simpa [interp2_bvar, cons] using hx)).2.2))
    case _ => exact hlev.1
    case _ => exact hlev.2
  · rw [eqReflTyP, interp2_pi, interp2_sort]
    refine piR_congr fun Aset hAset => ?_
    rw [interp2_pi]
    simp only [interp2_bvar, cons]
    exact piR_congr fun x hx => (hstep Aset x hAset hx).1

/-! ### The two installs -/

/-- **`Eq`, installed at the P tier** — the tier's one `eq_lawP`
bespoke cons. -/
theorem extendEqP (mp : EnvS2PM V μ env)
    (hfresh : env.find? eqName = none)
    (hbase : EnvS V ⟨eqA :: env.consts⟩)
    (hag : ∀ n, n ≠ eqA.name → mp.base2.base.cval n = hbase.cval n)
    (hcv : ∀ ψ, hbase.cval eqA.name ψ = eqValT ψ) :
    Nonempty (EnvS2PM V μ ⟨eqA :: env.consts⟩) := by
  refine declStepPM_of_basis_cons_eqrow mp (A := eqValT2) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h) (by decide)
    (Or.inl (fun _ h => nomatch h))
    hbase hag
    (fun ψ => by rw [hcv ψ]; exact eqValT2_erase ψ)
    (fun ψ k => AVExpr.liftN_eq_self _
      (VExpr.bvarsBelow.mono (Nat.zero_le k)
        (by rw [eqValT2_erase]; exact eqValT_closed ψ)) 1)
    (fun ψ₁ ψ₂ hp => eqValT2_congr
      (hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)))
    (fun ψ ρ => eqValT2_ok2 ψ ρ) (fun ψ ρ => eqValT2_validV ψ ρ)
    (fun ψ => ⟨_, denoteP_eqA_type ψ⟩) ?_ ?_ ?_
  · intro ψ ta h ρ
    rw [denoteP_eqA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact eqTyP_okP ψ ρ
  · intro ψ ta h ρ
    rw [denoteP_eqA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [eqTyP_interp]
    exact eqValT2_mem ψ ρ
  · intro m₂ hac
    refine eqLawP_of_tower m₂ fun ψ => ?_
    rw [hac, show eqName = eqA.name from rfl, acvalWith_self]

/-- **`Eq.refl`, installed at the P tier.** -/
theorem extendEqReflP (mp : EnvS2PM V μ env)
    (hE : env.find? eqName = some eqA)
    (hEv : ∀ ψ : Name → Nat, mp.base2.acval eqName ψ = eqValT2 ψ)
    (hfresh : env.find? eqReflA.name = none)
    (hbase : EnvS V ⟨eqReflA :: env.consts⟩)
    (hag : ∀ n, n ≠ eqReflA.name → mp.base2.base.cval n = hbase.cval n)
    (hcv : ∀ ψ, hbase.cval eqReflA.name ψ = eqReflValT ψ) :
    Nonempty (EnvS2PM V μ ⟨eqReflA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteP_eqReflTy (m := mp.base2) (A := eqReflValT2) (c₀ := eqReflA)
      ψ (by decide) hE hEv
  refine declStepPM_of_basis_cons mp (A := eqReflValT2) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    hbase hag
    (fun ψ => by rw [hcv ψ]; exact eqReflValT2_erase ψ)
    (fun ψ k => AVExpr.liftN_eq_self _
      (VExpr.bvarsBelow.mono (Nat.zero_le k)
        (by rw [eqReflValT2_erase]; exact eqReflValT_closed ψ)) 1)
    (fun ψ₁ ψ₂ hp => eqReflValT2_congr
      (hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)))
    (fun ψ ρ => eqReflValT2_ok2 ψ ρ)
    (fun ψ ρ => eqReflValT2_validV ψ ρ)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (eqReflTyP_data ψ ρ).1
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [(eqReflTyP_data ψ ρ).2]
    exact eqReflValT2_mem ψ ρ

/-! ## `Eq.rec`

Its six binders are pinned `.ifAllZero [u_1]` — the *motive* level's
zero test, not the type's — so the whole constant lives at one bit `b`
with `b = 0 ↔ ψ u_1 = 0`.  Its rule returns the minor premise, so the
only real content anywhere in the block is that the major premise's
membership forces `a = b` and the proof to be `pt`: an inhabitant of
`eqv a b` gives `a = b` by `mem_eqv`, and `eqv` is a truth value, so
the inhabitant is the canonical proof by `mem_univ_zero`.

`eqRecValT2`'s membership and grading are the two items the ENDGAME E
seal recorded as owed; both are below. -/

/-- `Eq.rec`'s motive binder domain reading. -/
def eqRecMotiveTyP (ψ : Name → Nat) : AVExpr :=
  .pi 0 1 (.bvar 1) (.pi 0 1 (eqSpineP ψ 2 1 0) (.sort (ψ u1N)))

/-- `Eq.rec`'s minor binder domain reading. -/
def eqRecMinorTyP (ψ : Name → Nat) : AVExpr :=
  .app (.app (.bvar 0) (.bvar 1)) (eqReflSpineP ψ 2 1)

/-- `Eq.rec`'s type reading. -/
def eqRecTyP (b : Nat) (ψ : Name → Nat) : AVExpr :=
  .pi 0 b (.sort (ψ uN))
    (.pi 0 b (.bvar 0)
      (.pi 0 b (eqRecMotiveTyP ψ)
        (.pi 0 b (eqRecMinorTyP ψ)
          (.pi 0 b (.bvar 3)
            (.pi 0 b (eqSpineP ψ 4 3 0)
              (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))))

/-- `Eq.rec`'s rule's RHS reading: the same four domains, over the
minor premise. -/
def eqRecRaP (b : Nat) (ψ : Name → Nat) : AVExpr :=
  .lam b (.sort (ψ uN))
    (.lam b (.bvar 0)
      (.lam b (eqRecMotiveTyP ψ)
        (.lam b (eqRecMinorTyP ψ) (.bvar 0))))

/-- The motive space: `∀ b, a = b → Sort u₁`. -/
noncomputable def eqRecMotiveSpace (V : Type w) [SetTheory V]
    (u1 : Nat) (Aset a : V) : V :=
  piR 1 Aset fun b => piR 1 (eqv a b) fun _ => (univ u1 : V)

theorem eqRecMotiveTyP_data {ψ : Name → Nat} {Aset a : V}
    (ρ : Nat → V) (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset) :
    interp2 V (cons a (cons Aset ρ)) (eqRecMotiveTyP ψ)
        = eqRecMotiveSpace V (ψ u1N) Aset a ∧
      AnnotOkP V (cons a (cons Aset ρ)) (eqRecMotiveTyP ψ) := by
  have hsp : ∀ b : V, b ∈ˢ Aset →
      interp2 V (cons b (cons a (cons Aset ρ))) (eqSpineP ψ 2 1 0)
          = eqv a b ∧
        AnnotOkP V (cons b (cons a (cons Aset ρ))) (eqSpineP ψ 2 1 0) ∧
        interp2 V (cons b (cons a (cons Aset ρ))) (eqSpineP ψ 2 1 0)
          ∈ˢ (univZero : V) := fun b hb =>
    eqSpineP_interp (ρ := cons b (cons a (cons Aset ρ)))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA ha hb
  have hdom : interp2 V (cons a (cons Aset ρ)) (AVExpr.bvar 1)
      = Aset := by simp [interp2_bvar, cons]
  refine ⟨?_, ?_⟩
  · rw [eqRecMotiveTyP, interp2_pi, eqRecMotiveSpace, hdom]
    refine piR_congr fun b hb => ?_
    rw [interp2_pi, (hsp b hb).1]
    exact piR_congr fun _ _ => interp2_sort V _ _
  · refine ⟨⟨trivial, fun b hb => ?_⟩,
      ⟨trivial, fun b hb => ?_, fun h => absurd h Nat.one_ne_zero⟩⟩
    · rw [hdom] at hb
      exact ⟨(hsp b hb).2.1.1, fun _ _ => trivial⟩
    · rw [hdom] at hb
      exact ⟨(hsp b hb).2.1.2, fun _ _ => trivial,
        fun h => absurd h Nat.one_ne_zero⟩

theorem eqRecMinorTyP_data {ψ : Name → Nat} {Aset a M : V}
    (ρ : Nat → V) (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset)
    (hM : M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a) :
    interp2 V (cons M (cons a (cons Aset ρ))) (eqRecMinorTyP ψ)
        = app (app M a) pt ∧
      AnnotOkP V (cons M (cons a (cons Aset ρ))) (eqRecMinorTyP ψ) ∧
      app (app M a) pt ∈ˢ (univ (ψ u1N) : V) := by
  obtain ⟨hrint, hrok⟩ := eqReflSpineP_data (ψ := ψ) (i := 2) (j := 1)
    (ρ := cons M (cons a (cons Aset ρ)))
    (by simp [cons]) (by simp [cons]) hA ha
  have hM0 : M ∈ˢ piR 1 Aset (fun b => piR 1 (eqv a b)
      fun _ => (univ (ψ u1N) : V)) := hM
  have hMa : app M a ∈ˢ piR 1 (eqv a a) fun _ => (univ (ψ u1N) : V) :=
    app_mem_piR_pos Nat.one_ne_zero hM0 ha
  have hMap : app (app M a) pt ∈ˢ (univ (ψ u1N) : V) :=
    app_mem_piR_pos Nat.one_ne_zero hMa (pt_mem_eqv_self a)
  have hMb : interp2 V (cons M (cons a (cons Aset ρ)))
      (AVExpr.bvar 0) = M := by simp [interp2_bvar, cons]
  have hab : interp2 V (cons M (cons a (cons Aset ρ)))
      (AVExpr.bvar 1) = a := by simp [interp2_bvar, cons]
  refine ⟨?_, ⟨?_, ?_⟩, hMap⟩
  · rw [eqRecMinorTyP, interp2_app, interp2_app, hrint, hMb, hab]
  · rw [eqRecMinorTyP, AnnotOk2_app]
    refine ⟨?_, hrok.1, 1, eqv a a, fun _ => (univ (ψ u1N) : V), ?_,
      by rw [hrint]; exact pt_mem_eqv_self a,
      fun h => absurd h Nat.one_ne_zero⟩
    · rw [AnnotOk2_app]
      exact ⟨trivial, trivial, 1, Aset,
        fun b => piR 1 (eqv a b) fun _ => (univ (ψ u1N) : V),
        by rw [hMb]; exact hM0, by rw [hab]; exact ha,
        fun h => absurd h Nat.one_ne_zero⟩
    · rw [interp2_app, hMb, hab]; exact hMa
  · exact ⟨⟨trivial, trivial⟩, hrok.2⟩

/-- **The major premise collapses the block**: an inhabitant of
`eqv a b` identifies `a` with `b` and is itself the canonical proof.
This is `Eq.rec`'s entire iota content, and it is why the layer does
not carry the constant at all (`eqRec_derivable`). -/
theorem eqRec_major_collapse {a b h : V} (hh : h ∈ˢ eqv a b) :
    a = b ∧ h = pt :=
  ⟨mem_eqv hh, mem_univ_zero (univ_zero (V := V) ▸ eqv_mem_univZero a b) hh⟩

/-! ### The tower, bit-cleaned

`eqRecValT2` carries the *type's* result sort `ψ u_1 + 1` at the
motive domain's inner binder where the reading carries `pwBit … .never
= 1`.  The two agree on zero-ness and on nothing else is read, so they
are `BitAgree` — which is the whole distance between the tower the
ENDGAME E seal built and the tower this block's walk wants. -/

/-- The tower with the reading's own numerals. -/
def eqRecRaTower (b : Nat) (ψ : Name → Nat) : AVExpr :=
  .lam b (.sort (ψ uN))
    (.lam b (.bvar 0)
      (.lam b (eqRecMotiveTyP ψ)
        (.lam b (eqRecMinorTyP ψ)
          (.lam b (.bvar 3)
            (.lam b (eqSpineP ψ 4 3 0) (.bvar 2))))))

theorem bitAgree_eqRecValT2 (ψ : Name → Nat) :
    AVExpr.BitAgree (eqRecRaTower (pwBit ψ (.ifAllZero [u1N])) ψ)
      (eqRecValT2 ψ) :=
  .lam Iff.rfl (.sort _)
    (.lam Iff.rfl (.bvar 0)
      (.lam Iff.rfl
        (.pi Iff.rfl (.bvar 1)
          (.pi (Iff.intro (fun h => absurd h Nat.one_ne_zero)
              (fun h => absurd h (Nat.succ_ne_zero _)))
            (AVExpr.BitAgree.refl _) (.sort _)))
        (.lam Iff.rfl (AVExpr.BitAgree.refl _)
          (.lam Iff.rfl (.bvar 3)
            (.lam Iff.rfl (AVExpr.BitAgree.refl _) (.bvar 2))))))

/-- **`Eq.rec`'s tower is graded and inhabits its type's reading** —
the two items the ENDGAME E seal recorded as owed, taken in one walk
(`AnnotOkP_lam_mem` six times).  The only content is at the bottom:
the major premise collapses `b` onto `a` and itself onto `pt`, and the
minor premise is already there. -/
theorem eqRecRaTower_data {b : Nat} (ψ : Name → Nat)
    (hz : b = 0 ↔ ψ u1N = 0) (ρ : Nat → V) :
    AnnotOkP V ρ (eqRecRaTower b ψ) ∧
      interp2 V ρ (eqRecRaTower b ψ)
        ∈ˢ interp2 V ρ (eqRecTyP b ψ) := by
  have hzero : ∀ x : V, x ∈ˢ (univ (ψ u1N) : V) → b = 0 →
      x ∈ˢ (univZero : V) := fun x hx hb => by
    rw [← univ_zero, ← hz.mp hb]; exact hx
  -- level 6: the body, at a fixed major premise
  have h6 : ∀ Aset a M mn bb : V, Aset ∈ˢ (univ (ψ uN) : V) →
      a ∈ˢ Aset → M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      mn ∈ˢ app (app M a) pt → bb ∈ˢ Aset →
      AnnotOkP V (cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
          (.lam b (eqSpineP ψ 4 3 0) (.bvar 2)) ∧
        interp2 V (cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
            (.lam b (eqSpineP ψ 4 3 0) (.bvar 2))
          ∈ˢ piR b (eqv a bb) (fun h => app (app M bb) h) := by
    intro Aset a M mn bb hA ha hM hmn hbb
    obtain ⟨hsint, hsok, -⟩ := eqSpineP_interp
      (ρ := cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
      (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA ha hbb
    have hM0 : M ∈ˢ piR 1 Aset (fun x => piR 1 (eqv a x)
        fun _ => (univ (ψ u1N) : V)) := hM
    have hMb : app M bb ∈ˢ piR 1 (eqv a bb)
        fun _ => (univ (ψ u1N) : V) :=
      app_mem_piR_pos Nat.one_ne_zero hM0 hbb
    have key : ∀ h : V, h ∈ˢ eqv a bb →
        app (app M bb) h = app (app M a) pt ∧
          app (app M bb) h ∈ˢ (univ (ψ u1N) : V) := by
      intro h hh
      obtain ⟨hab, hpt⟩ := eqRec_major_collapse (V := V) hh
      refine ⟨by rw [hab, hpt], ?_⟩
      exact app_mem_piR_pos Nat.one_ne_zero hMb hh
    have hstep := AnnotOkP_lam_mem (V := V) (b := b)
      (Aa := eqSpineP ψ 4 3 0) (bd := .bvar 2)
      (F := fun h => app (app M bb) h) hsok
      (fun h hh => by
        rw [hsint] at hh
        refine ⟨⟨trivial, trivial⟩, ?_⟩
        rw [show interp2 V (cons h (cons bb (cons mn (cons M
            (cons a (cons Aset ρ)))))) (AVExpr.bvar 2) = mn
          from by simp [interp2_bvar, cons], (key h hh).1]
        exact hmn)
      (fun hb h hh => by
        rw [hsint] at hh
        exact hzero _ (key h hh).2 hb)
    rw [hsint] at hstep
    exact hstep
  -- level 5
  have h5 : ∀ Aset a M mn : V, Aset ∈ˢ (univ (ψ uN) : V) →
      a ∈ˢ Aset → M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      mn ∈ˢ app (app M a) pt →
      AnnotOkP V (cons mn (cons M (cons a (cons Aset ρ))))
          (.lam b (.bvar 3) (.lam b (eqSpineP ψ 4 3 0) (.bvar 2))) ∧
        interp2 V (cons mn (cons M (cons a (cons Aset ρ))))
            (.lam b (.bvar 3) (.lam b (eqSpineP ψ 4 3 0) (.bvar 2)))
          ∈ˢ piR b Aset
            (fun bb => piR b (eqv a bb) fun h => app (app M bb) h) := by
    intro Aset a M mn hA ha hM hmn
    have hdom : interp2 V (cons mn (cons M (cons a (cons Aset ρ))))
        (AVExpr.bvar 3) = Aset := by simp [interp2_bvar, cons]
    have hstep := AnnotOkP_lam_mem (V := V) (b := b)
      (Aa := AVExpr.bvar 3)
      (bd := .lam b (eqSpineP ψ 4 3 0) (.bvar 2))
      (F := fun bb => piR b (eqv a bb) fun h => app (app M bb) h)
      ⟨trivial, trivial⟩
      (fun bb hbb => h6 Aset a M mn bb hA ha hM hmn
        (by rwa [hdom] at hbb))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hdom] at hstep
    exact hstep
  -- level 4
  have h4 : ∀ Aset a M : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      AnnotOkP V (cons M (cons a (cons Aset ρ)))
          (.lam b (eqRecMinorTyP ψ)
            (.lam b (.bvar 3)
              (.lam b (eqSpineP ψ 4 3 0) (.bvar 2)))) ∧
        interp2 V (cons M (cons a (cons Aset ρ)))
            (.lam b (eqRecMinorTyP ψ)
              (.lam b (.bvar 3)
                (.lam b (eqSpineP ψ 4 3 0) (.bvar 2))))
          ∈ˢ piR b (app (app M a) pt) (fun _ => piR b Aset
            (fun bb => piR b (eqv a bb) fun h => app (app M bb) h)) := by
    intro Aset a M hA ha hM
    obtain ⟨hmint, hmok, -⟩ := eqRecMinorTyP_data ρ hA ha hM
    have hstep := AnnotOkP_lam_mem (V := V) (b := b)
      (Aa := eqRecMinorTyP ψ)
      (F := fun _ => piR b Aset
        (fun bb => piR b (eqv a bb) fun h => app (app M bb) h))
      hmok
      (fun mn hmn => h5 Aset a M mn hA ha hM (by rwa [hmint] at hmn))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hmint] at hstep
    exact hstep
  -- level 3
  have h3 : ∀ Aset a : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      AnnotOkP V (cons a (cons Aset ρ))
          (.lam b (eqRecMotiveTyP ψ)
            (.lam b (eqRecMinorTyP ψ)
              (.lam b (.bvar 3)
                (.lam b (eqSpineP ψ 4 3 0) (.bvar 2))))) ∧
        interp2 V (cons a (cons Aset ρ))
            (.lam b (eqRecMotiveTyP ψ)
              (.lam b (eqRecMinorTyP ψ)
                (.lam b (.bvar 3)
                  (.lam b (eqSpineP ψ 4 3 0) (.bvar 2)))))
          ∈ˢ piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
            (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
              (fun bb => piR b (eqv a bb)
                fun h => app (app M bb) h))) := by
    intro Aset a hA ha
    obtain ⟨hmint, hmok⟩ := eqRecMotiveTyP_data ρ hA ha
    have hstep := AnnotOkP_lam_mem (V := V) (b := b)
      (Aa := eqRecMotiveTyP ψ)
      (F := fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
        (fun bb => piR b (eqv a bb) fun h => app (app M bb) h)))
      hmok
      (fun M hM => h4 Aset a M hA ha (by rwa [hmint] at hM))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hmint] at hstep
    exact hstep
  -- level 2
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ (ψ uN) : V) →
      AnnotOkP V (cons Aset ρ)
          (.lam b (.bvar 0)
            (.lam b (eqRecMotiveTyP ψ)
              (.lam b (eqRecMinorTyP ψ)
                (.lam b (.bvar 3)
                  (.lam b (eqSpineP ψ 4 3 0) (.bvar 2)))))) ∧
        interp2 V (cons Aset ρ)
            (.lam b (.bvar 0)
              (.lam b (eqRecMotiveTyP ψ)
                (.lam b (eqRecMinorTyP ψ)
                  (.lam b (.bvar 3)
                    (.lam b (eqSpineP ψ 4 3 0) (.bvar 2))))))
          ∈ˢ piR b Aset (fun a =>
            piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
              (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
                (fun bb => piR b (eqv a bb)
                  fun h => app (app M bb) h)))) := by
    intro Aset hA
    have hdom : interp2 V (cons Aset ρ) (AVExpr.bvar 0) = Aset := by
      simp [interp2_bvar, cons]
    have hstep := AnnotOkP_lam_mem (V := V) (b := b)
      (Aa := AVExpr.bvar 0)
      (F := fun a => piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
          (fun bb => piR b (eqv a bb) fun h => app (app M bb) h))))
      ⟨trivial, trivial⟩
      (fun a ha => h3 Aset a hA (by rwa [hdom] at ha))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hdom] at hstep
    exact hstep
  have hstep := AnnotOkP_lam_mem (V := V) (b := b)
    (Aa := .sort (ψ uN))
    (F := fun Aset => piR b Aset (fun a =>
      piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
          (fun bb => piR b (eqv a bb) fun h => app (app M bb) h)))))
    ⟨trivial, trivial⟩
    (fun Aset hA => h2 Aset (by rwa [interp2_sort] at hA))
    (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
  refine ⟨hstep.1, ?_⟩
  rw [interp2_sort] at hstep
  refine (?_ : interp2 V ρ (eqRecTyP b ψ)
    = piR b (univ (ψ uN) : V) (fun Aset => piR b Aset (fun a =>
      piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
          (fun bb => piR b (eqv a bb)
            fun h => app (app M bb) h)))))) ▸ hstep.2
  -- the type reading's own six products, in the same order
  rw [eqRecTyP, interp2_pi, interp2_sort]
  refine piR_congr fun Aset hAset => ?_
  rw [interp2_pi]
  simp only [interp2_bvar, cons]
  refine piR_congr fun a ha => ?_
  rw [interp2_pi, (eqRecMotiveTyP_data ρ hAset ha).1]
  refine piR_congr fun M hM => ?_
  rw [interp2_pi, (eqRecMinorTyP_data ρ hAset ha hM).1]
  refine piR_congr fun mn _ => ?_
  rw [interp2_pi]
  simp only [interp2_bvar, cons]
  refine piR_congr fun bb hbb => ?_
  rw [interp2_pi,
    (eqSpineP_interp (ρ := cons bb (cons mn (cons M (cons a
        (cons Aset ρ))))) (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons])
      hAset ha hbb).1]
  refine piR_congr fun h _ => ?_
  simp [interp2_app, interp2_bvar, cons]

/-! ### The two readings -/

/-- **`Eq.rec`'s type reading.** -/
theorem denoteP_eqRecA_type (ψ : Name → Nat)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValT2 ψ)
    (hRv : ∀ ψ : Name → Nat, m.acval eqReflName ψ = eqReflValT2 ψ) :
    denoteP (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ 0 eqRecA.toConstantVal.type
      = some (eqRecTyP (pwBit ψ (.ifAllZero [u1N])) ψ) := by
  have hEc : ∀ d : Nat,
      denoteP (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ d (.const eqName [.param uN])
        = some (eqValT2 ψ) := by
    intro d
    rw [denoteP_eqLeaf (m := m) (A := A) ψ (Level.param uN)
        (by decide) hE d,
      show ([Level.param uN] : List Level)
        = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN], hEv]
  have hRc : ∀ d : Nat,
      denoteP (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ d (.const eqReflName [.param uN])
        = some (eqReflValT2 ψ) := by
    intro d
    have hf' : (⟨eqRecA :: env.consts⟩ : Env).find? eqReflName
        = some eqReflA := by
      rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hR
    rw [denoteP_const hf' (by rfl), acvalWith_ne (by decide),
      show Level.substFn ψ eqReflA.toConstantVal.levelParams
        [Level.param uN] = Level.substFn ψ [uN]
          (List.map Level.param [uN]) from rfl,
      Level.substFn_param_self ψ [uN], hRv]
  rw [show eqRecA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
            (Expr.forallE (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "b") (.bvar 1)
                (Expr.forallE (Name.anonymous.str "t")
                  (.app (.app (.app (.const eqName [.param uN])
                    (.bvar 2)) (.bvar 1)) (.bvar 0))
                  (.sort (.param u1N))
                  { bi := .default, pw := .never })
                { bi := .default, pw := .never })
              (Expr.forallE (Name.anonymous.str "refl")
                (.app (.app (.bvar 0) (.bvar 1))
                  (.app (.app (.const eqReflName [.param uN])
                    (.bvar 2)) (.bvar 1)))
                (Expr.forallE (Name.anonymous.str "b") (.bvar 3)
                  (Expr.forallE (Name.anonymous.str "t")
                    (.app (.app (.app (.const eqName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 0))
                    (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
                    { bi := .default, pw := .ifAllZero [u1N] })
                  { bi := .implicit, pw := .ifAllZero [u1N] })
                { bi := .default, pw := .ifAllZero [u1N] })
              { bi := .implicit, pw := .ifAllZero [u1N] })
            { bi := .implicit, pw := .ifAllZero [u1N] })
          { bi := .implicit, pw := .ifAllZero [u1N] } from rfl]
  simp [denoteP_forallE, denoteP_sort, denoteP_app, denoteP_fvar,
    Expr.instantiate1, eqRecTyP, eqRecMotiveTyP, eqRecMinorTyP,
    eqSpineP, eqReflSpineP, pwBit_never, hEc, hRc, Level.eval]

/-- **`Eq.rec`'s rule's RHS reading.** -/
theorem denoteP_eqRec_rhs (ψ : Name → Nat)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValT2 ψ)
    (hRv : ∀ ψ : Name → Nat, m.acval eqReflName ψ = eqReflValT2 ψ) :
    denoteP (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ 0 eqRecRule.rhs
      = some (eqRecRaP (pwBit ψ (.ifAllZero [u1N])) ψ) := by
  have hEc : ∀ d : Nat,
      denoteP (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ d (.const eqName [.param uN])
        = some (eqValT2 ψ) := by
    intro d
    rw [denoteP_eqLeaf (m := m) (A := A) ψ (Level.param uN)
        (by decide) hE d,
      show ([Level.param uN] : List Level)
        = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN], hEv]
  have hRc : ∀ d : Nat,
      denoteP (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ d (.const eqReflName [.param uN])
        = some (eqReflValT2 ψ) := by
    intro d
    have hf' : (⟨eqRecA :: env.consts⟩ : Env).find? eqReflName
        = some eqReflA := by
      rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hR
    rw [denoteP_const hf' (by rfl), acvalWith_ne (by decide),
      show Level.substFn ψ eqReflA.toConstantVal.levelParams
        [Level.param uN] = Level.substFn ψ [uN]
          (List.map Level.param [uN]) from rfl,
      Level.substFn_param_self ψ [uN], hRv]
  simp only [eqRecRule]
  simp [denoteP_lam, denoteP_forallE, denoteP_sort, denoteP_app,
    denoteP_fvar, Expr.instantiate1, eqRecRaP, eqRecMotiveTyP,
    eqRecMinorTyP, eqSpineP, eqReflSpineP, pwBit_never, hEc, hRc,
    Level.eval]

/-! ### The RHS tower and the two firing sides -/

/-- The product the RHS tower inhabits. -/
noncomputable def eqRecRaSpace (V : Type w) [SetTheory V]
    (b u u1 : Nat) : V :=
  piR b (univ u : V) fun Aset => piR b Aset fun a =>
    piR b (eqRecMotiveSpace V u1 Aset a) fun M =>
      piR b (app (app M a) pt) fun _ => app (app M a) pt

theorem eqRecRaP_data {b : Nat} (ψ : Name → Nat)
    (hz : b = 0 ↔ ψ u1N = 0) (ρ : Nat → V) :
    AnnotOkP V ρ (eqRecRaP b ψ) ∧
      interp2 V ρ (eqRecRaP b ψ)
        ∈ˢ eqRecRaSpace V b (ψ uN) (ψ u1N) := by
  have hzero : ∀ x : V, x ∈ˢ (univ (ψ u1N) : V) → b = 0 →
      x ∈ˢ (univZero : V) := fun x hx hb => by
    rw [← univ_zero, ← hz.mp hb]; exact hx
  have h4 : ∀ Aset a M : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      AnnotOkP V (cons M (cons a (cons Aset ρ)))
          (.lam b (eqRecMinorTyP ψ) (.bvar 0)) ∧
        interp2 V (cons M (cons a (cons Aset ρ)))
            (.lam b (eqRecMinorTyP ψ) (.bvar 0))
          ∈ˢ piR b (app (app M a) pt) (fun _ => app (app M a) pt) := by
    intro Aset a M hA ha hM
    obtain ⟨hmint, hmok, hmuniv⟩ := eqRecMinorTyP_data ρ hA ha hM
    have hstep := AnnotOkP_lam_mem (V := V) (b := b)
      (Aa := eqRecMinorTyP ψ) (bd := .bvar 0)
      (F := fun _ => app (app M a) pt) hmok
      (fun mn hmn => by
        rw [hmint] at hmn
        exact ⟨⟨trivial, trivial⟩, by
          rw [show interp2 V (cons mn (cons M (cons a (cons Aset ρ))))
            (AVExpr.bvar 0) = mn from by simp [interp2_bvar, cons]]
          exact hmn⟩)
      (fun hb _ _ => hzero _ hmuniv hb)
    rw [hmint] at hstep
    exact hstep
  have h3 : ∀ Aset a : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      AnnotOkP V (cons a (cons Aset ρ))
          (.lam b (eqRecMotiveTyP ψ)
            (.lam b (eqRecMinorTyP ψ) (.bvar 0))) ∧
        interp2 V (cons a (cons Aset ρ))
            (.lam b (eqRecMotiveTyP ψ)
              (.lam b (eqRecMinorTyP ψ) (.bvar 0)))
          ∈ˢ piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
            (fun M => piR b (app (app M a) pt)
              (fun _ => app (app M a) pt)) := by
    intro Aset a hA ha
    obtain ⟨hmint, hmok⟩ := eqRecMotiveTyP_data ρ hA ha
    have hstep := AnnotOkP_lam_mem (V := V) (b := b)
      (Aa := eqRecMotiveTyP ψ)
      (F := fun M => piR b (app (app M a) pt)
        (fun _ => app (app M a) pt)) hmok
      (fun M hM => h4 Aset a M hA ha (by rwa [hmint] at hM))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hmint] at hstep
    exact hstep
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ (ψ uN) : V) →
      AnnotOkP V (cons Aset ρ)
          (.lam b (.bvar 0) (.lam b (eqRecMotiveTyP ψ)
            (.lam b (eqRecMinorTyP ψ) (.bvar 0)))) ∧
        interp2 V (cons Aset ρ)
            (.lam b (.bvar 0) (.lam b (eqRecMotiveTyP ψ)
              (.lam b (eqRecMinorTyP ψ) (.bvar 0))))
          ∈ˢ piR b Aset (fun a =>
            piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
              (fun M => piR b (app (app M a) pt)
                (fun _ => app (app M a) pt))) := by
    intro Aset hA
    have hdom : interp2 V (cons Aset ρ) (AVExpr.bvar 0) = Aset := by
      simp [interp2_bvar, cons]
    have hstep := AnnotOkP_lam_mem (V := V) (b := b)
      (Aa := AVExpr.bvar 0)
      (F := fun a => piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt)
          (fun _ => app (app M a) pt)))
      ⟨trivial, trivial⟩
      (fun a ha => h3 Aset a hA (by rwa [hdom] at ha))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hdom] at hstep
    exact hstep
  have hstep := AnnotOkP_lam_mem (V := V) (b := b)
    (Aa := .sort (ψ uN))
    (F := fun Aset => piR b Aset (fun a =>
      piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt)
          (fun _ => app (app M a) pt))))
    ⟨trivial, trivial⟩
    (fun Aset hA => h2 Aset (by rwa [interp2_sort] at hA))
    (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
  rw [interp2_sort] at hstep
  exact ⟨hstep.1, hstep.2⟩

/-- **`Eq.rec`'s recursor tower fires to the minor premise** — at
`b ≠ 0` by six `app_lamR_pos`, at `b = 0` because the motive's fibre
is then a truth value and the minor premise *is* the canonical
proof. -/
theorem eqRecRaTower_app₆ {b : Nat} (ψ : Name → Nat)
    (hz : b = 0 ↔ ψ u1N = 0) (ρ : Nat → V) {Aset a M mn bb h : V}
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset)
    (hM : M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a)
    (hmn : mn ∈ˢ app (app M a) pt) (hbb : bb ∈ˢ Aset)
    (hh : h ∈ˢ eqv a bb) :
    app (app (app (app (app (app
        (interp2 V ρ (eqRecRaTower b ψ)) Aset) a) M) mn) bb) h = mn := by
  obtain ⟨hmint, -, hmuniv⟩ := eqRecMinorTyP_data ρ hA ha hM
  by_cases hb : b = 0
  · rw [eqRecRaTower, interp2_lam, hb, lamR_zero, app_pt, app_pt,
      app_pt, app_pt, app_pt, app_pt]
    have h0 : app (app M a) pt ∈ˢ (univ 0 : V) := by
      rw [← hz.mp hb]; exact hmuniv
    exact (mem_univ_zero h0 hmn).symm
  · obtain ⟨hmoint, -⟩ := eqRecMotiveTyP_data ρ hA ha
    obtain ⟨hsint, -, -⟩ := eqSpineP_interp
      (ρ := cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
      (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA ha hbb
    rw [eqRecRaTower, interp2_lam, interp2_sort, app_lamR_pos hb hA,
      interp2_lam,
      show interp2 V (cons Aset ρ) (AVExpr.bvar 0) = Aset
        from by simp [interp2_bvar, cons],
      app_lamR_pos hb ha,
      interp2_lam, hmoint, app_lamR_pos hb hM,
      interp2_lam, hmint, app_lamR_pos hb hmn,
      interp2_lam,
      show interp2 V (cons mn (cons M (cons a (cons Aset ρ))))
        (AVExpr.bvar 3) = Aset from by simp [interp2_bvar, cons],
      app_lamR_pos hb hbb,
      interp2_lam, hsint, app_lamR_pos hb hh]
    simp [interp2_bvar, cons]

/-- …and the RHS tower's four-fold application is the same value. -/
theorem eqRecRaP_app₄ {b : Nat} (ψ : Name → Nat)
    (hz : b = 0 ↔ ψ u1N = 0) (ρ : Nat → V) {Aset a M mn : V}
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset)
    (hM : M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a)
    (hmn : mn ∈ˢ app (app M a) pt) :
    app (app (app (app (interp2 V ρ (eqRecRaP b ψ)) Aset) a) M) mn
      = mn := by
  obtain ⟨hmint, -, hmuniv⟩ := eqRecMinorTyP_data ρ hA ha hM
  by_cases hb : b = 0
  · rw [eqRecRaP, interp2_lam, hb, lamR_zero, app_pt, app_pt, app_pt,
      app_pt]
    have h0 : app (app M a) pt ∈ˢ (univ 0 : V) := by
      rw [← hz.mp hb]; exact hmuniv
    exact (mem_univ_zero h0 hmn).symm
  · obtain ⟨hmoint, -⟩ := eqRecMotiveTyP_data ρ hA ha
    rw [eqRecRaP, interp2_lam, interp2_sort, app_lamR_pos hb hA,
      interp2_lam,
      show interp2 V (cons Aset ρ) (AVExpr.bvar 0) = Aset
        from by simp [interp2_bvar, cons],
      app_lamR_pos hb ha,
      interp2_lam, hmoint, app_lamR_pos hb hM,
      interp2_lam, hmint, app_lamR_pos hb hmn]
    simp [interp2_bvar, cons]

end Eq

end Setlec.SetR.Interp2
