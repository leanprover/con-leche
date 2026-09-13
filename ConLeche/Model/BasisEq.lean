module

public import ConLeche.Model.BasisQuot
import ConLeche.Semantics.BasisRules
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen

public section

/-!
# The `Eq` block, P tier (task #161, ENDGAME H)

The one block the layer does not carry: there is no `BConst` for `Eq`,
so nothing here goes through `BConst.typeAV`/`BitAgree`/`bval_mem_type`
— every type reading's grading and membership is discharged against
the block's **own** towers (`Interp/EqTowerP.lean`), which is exactly
why the ENDGAME E seal built them first.

Two structural consequences:

* the `Eq` cons is the tier's one `eq_law`-bespoke cons
  (`eqLaw_cons_fresh`'s side condition is `eqName ≠ c₀.name`), and it
  is discharged by `eqLaw_of_tower` through
  `declStep_preserves_of_basis_cons_eqrow`;
* `Eq.rec`'s stored rule returns its **minor premise**, so its fired
  equality is an identity between two collapsed towers rather than a
  value law — and the only real content is that the major premise's
  membership forces `a = b` and the proof to be `pt`.

The three constants' bits are forced, not chosen (ENDGAME E §1):
`Eq`'s three binders are `.never`, `Eq.refl`'s two are
`.ifAllZero []`, and `Eq.rec`'s six are `.ifAllZero [u_1]`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm eqValT eqReflValT eqRecValT)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule uN u1N vN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

section Eq

open ConLeche (eqA eqReflA eqRecA eqName eqReflName)

variable {m : EnvModel V env} {A : (Name → Nat) → AnnotTerm}

/-! ## The two spines the block's types are built from -/

/-- `@Eq.{u} α a b`, read through the tower. -/
def eqSpine (ψ : Name → Nat) (i j k : Nat) : AnnotTerm :=
  .app (.app (.app (eqValAV ψ) (.bvar i)) (.bvar j)) (.bvar k)

/-- `@Eq.refl.{u} α a`, read through the tower. -/
def eqReflSpine (ψ : Name → Nat) (i j : Nat) : AnnotTerm :=
  .app (.app (eqReflValAV ψ) (.bvar i)) (.bvar j)

theorem eqSpine_interp {ψ : Name → Nat} {i j k : Nat} {ρ : Nat → V}
    {Aset a b : V} (hi : ρ i = Aset) (hj : ρ j = a) (hk : ρ k = b)
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset) (hb : b ∈ˢ Aset) :
    interp V ρ (eqSpine ψ i j k) = eqv a b ∧
      WellDenotedV V ρ (eqSpine ψ i j k) ∧
      interp V ρ (eqSpine ψ i j k) ∈ˢ (univZero : V) := by
  have hAi : interp V ρ (AnnotTerm.bvar i) = Aset := by
    rw [interp_bvar, hi]
  have haj : interp V ρ (AnnotTerm.bvar j) = a := by
    rw [interp_bvar, hj]
  have hbk : interp V ρ (AnnotTerm.bvar k) = b := by
    rw [interp_bvar, hk]
  obtain ⟨hok, hz⟩ := eqValAV_app₃_okP ψ ρ (Aa := .bvar i) (la := .bvar j)
    (ra := .bvar k) ⟨trivial, trivial⟩ ⟨trivial, trivial⟩
    ⟨trivial, trivial⟩ (by rw [hAi]; exact hA)
    (by rw [hAi, haj]; exact ha) (by rw [hAi, hbk]; exact hb)
  refine ⟨?_, hok, hz⟩
  rw [eqSpine, interp_app, interp_app, interp_app, hAi, haj, hbk,
    eqValAV_app₃ ψ ρ Aset a b hA ha hb]

theorem eqReflSpine_data {ψ : Name → Nat} {i j : Nat} {ρ : Nat → V}
    {Aset a : V} (hi : ρ i = Aset) (hj : ρ j = a)
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset) :
    interp V ρ (eqReflSpine ψ i j) = (pt : V) ∧
      WellDenotedV V ρ (eqReflSpine ψ i j) := by
  have hpt : interp V ρ (eqReflValAV ψ) = (pt : V) :=
    eqReflValAV_interp ψ ρ
  have hAi : interp V ρ (AnnotTerm.bvar i) = Aset := by
    rw [interp_bvar, hi]
  have haj : interp V ρ (AnnotTerm.bvar j) = a := by
    rw [interp_bvar, hj]
  have h1 := WellDenotedV_app_pt (S := (univ (ψ uN) : V))
    (a := AnnotTerm.bvar i) (eqReflValAV_wellDenotedV ψ ρ) hpt
    ⟨trivial, trivial⟩ (by rw [hAi]; exact hA)
  have h2 := WellDenotedV_app_pt (S := Aset) (a := AnnotTerm.bvar j)
    h1.1 h1.2 ⟨trivial, trivial⟩ (by rw [haj]; exact ha)
  exact ⟨h2.2, h2.1⟩

/-! ## `Eq` and `Eq.refl` -/

/-- `Eq`'s type reading: three graph-regime binders. -/
@[expose] def eqTy (ψ : Name → Nat) : AnnotTerm :=
  .pi 0 1 (.sort (ψ uN)) (.pi 0 1 (.bvar 0) (.pi 0 1 (.bvar 1) (.sort 0)))

/-- `Eq.refl`'s type reading: two squash-regime binders over the
spine. -/
def eqReflTy (ψ : Name → Nat) : AnnotTerm :=
  .pi 0 0 (.sort (ψ uN)) (.pi 0 0 (.bvar 0) (eqSpine ψ 1 0 0))

/-- **`Eq`'s type reading.** -/
theorem denoteMeta_eqA_type
    {acval : Name → (Name → Nat) → AnnotTerm} (ψ : Name → Nat) :
    denoteMeta acval ⟨eqA :: env.consts⟩ ψ 0 eqA.toConstantVal.type
      = some (eqTy ψ) := by
  simp [eqA, ConstantInfo.toConstantVal, denoteMeta_forallE, denoteMeta_sort,
    denoteMeta_fvar, Expr.instantiate1, eqTy, pwBit_never, Level.eval, uN]

theorem eqTy_wellDenotedV (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (eqTy ψ) :=
  ⟨⟨trivial, fun _ _ => ⟨trivial, fun _ _ => ⟨trivial,
      fun _ _ => trivial⟩⟩⟩,
    ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => ⟨trivial,
        fun _ _ => trivial, fun h => absurd h Nat.one_ne_zero⟩,
      fun h => absurd h Nat.one_ne_zero⟩,
    fun h => absurd h Nat.one_ne_zero⟩⟩

theorem eqTy_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqTy ψ)
      = piR 1 (univ (ψ uN) : V)
          (fun a => piR 1 a (fun _ => piR 1 a (fun _ => univZero))) := by
  rw [eqTy, interp_pi, interp_sort]
  refine piR_congr fun a _ => ?_
  rw [interp_pi]
  simp only [interp_bvar, cons]
  refine piR_congr fun x _ => ?_
  rw [interp_pi]
  simp only [interp_bvar, interp_sort, cons]
  exact piR_congr fun _ _ => univ_zero

/-- **`Eq.refl`'s type reading.**  Stated at *any* extension whose
cons is not `Eq`, because `Eq.rec`'s row reads it as its fired
constructor's telescope. -/
theorem denoteMeta_eqReflTy {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = eqName)
    (hE : env.find? eqName = some eqA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValAV ψ) :
    denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ 0
        eqReflA.toConstantVal.type
      = some (eqReflTy ψ) := by
  have hEc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const eqName [.param uN]) = some (eqValAV ψ) := by
    intro d
    rw [denoteMeta_eqLeaf (m := m) (A := A) ψ (Level.param uN) hne hE d,
      show ([Level.param uN] : List Level)
        = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN], hEv]
  rw [show eqReflA.toConstantVal.type
      = Expr.forallE (.sort (.param uN))
          (Expr.forallE (.bvar 0)
            (.app (.app (.app (.const eqName [.param uN]) (.bvar 1))
              (.bvar 0)) (.bvar 0))
            { pw := .ifAllZero [] })
          { pw := .ifAllZero [] } from rfl]
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
    Expr.instantiate1, eqReflTy, eqSpine, pwBit_ifAllZero_nil, hEc,
    Level.eval]

theorem eqReflTy_data (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (eqReflTy ψ) ∧
      interp V ρ (eqReflTy ψ)
        = piR 0 (univ (ψ uN) : V) (fun a => piR 0 a (fun x => eqv x x)) := by
  have hstep : ∀ Aset x : V, Aset ∈ˢ (univ (ψ uN) : V) → x ∈ˢ Aset →
      interp V (cons x (cons Aset ρ)) (eqSpine ψ 1 0 0) = eqv x x ∧
      WellDenotedV V (cons x (cons Aset ρ)) (eqSpine ψ 1 0 0) ∧
      interp V (cons x (cons Aset ρ)) (eqSpine ψ 1 0 0)
        ∈ˢ (univZero : V) := by
    intro Aset x hA hx
    exact eqSpine_interp (ρ := cons x (cons Aset ρ))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA hx hx
  constructor
  · rw [eqReflTy]
    refine (WellDenotedV_pi_zero (Aa := .sort (ψ uN)) ⟨trivial, trivial⟩
      ?_ ?_).1
    all_goals (
      intro Aset hAset
      rw [interp_sort] at hAset
      have hlev := WellDenotedV_pi_zero (Aa := AnnotTerm.bvar 0)
        (ρ := cons Aset ρ) ⟨trivial, trivial⟩
        (fun x hx => (hstep Aset x hAset
          (by simpa [interp_bvar, cons] using hx)).2.1)
        (fun x hx => (hstep Aset x hAset
          (by simpa [interp_bvar, cons] using hx)).2.2))
    case _ => exact hlev.1
    case _ => exact hlev.2
  · rw [eqReflTy, interp_pi, interp_sort]
    refine piR_congr fun Aset hAset => ?_
    rw [interp_pi]
    simp only [interp_bvar, cons]
    exact piR_congr fun x hx => (hstep Aset x hAset hx).1

/-! ### The two installs -/

/-- **`Eq`, installed at the P tier** — the tier's one `eq_law`
bespoke cons. -/
theorem extendEq (mp : EnvModelM V μ env)
    (hfresh : env.find? eqName = none)
    (hwf : EnvWF ⟨eqA :: env.consts⟩) :
    ∃ mp' : EnvModelM V μ ⟨eqA :: env.consts⟩,
      mp'.base2.acval
        = acvalWith mp.base2.acval eqA.name eqValAV := by
  refine declStep_preserves_of_basis_cons_eqrow mp (A := eqValAV) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h) (by decide)
    (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf
      (fun ψ => by rw [eqValAV_erase ψ]; exact eqValT_closed ψ)
      rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT eqA.name ψ
          = none from rfl] at hp
        exact nomatch hp)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le k)
        (by rw [eqValAV_erase]; exact eqValT_closed ψ)) 1)
    (fun ψ₁ ψ₂ hp => eqValAV_congr
      (hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)))
    (fun ψ ρ => eqValAV_wellDenoted ψ ρ) (fun ψ ρ => eqValAV_validV ψ ρ)
    (fun ψ => ⟨_, denoteMeta_eqA_type ψ⟩) ?_ ?_ ?_
  · intro ψ ta h ρ
    rw [denoteMeta_eqA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact eqTy_wellDenotedV ψ ρ
  · intro ψ ta h ρ
    rw [denoteMeta_eqA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [eqTy_interp]
    exact eqValAV_mem ψ ρ
  · intro m₂ hac
    refine eqLaw_of_tower m₂ fun ψ => ?_
    rw [hac, show eqName = eqA.name from rfl, acvalWith_self]

/-- **`Eq.refl`, installed at the P tier.** -/
theorem extendEqRefl (mp : EnvModelM V μ env)
    (hE : env.find? eqName = some eqA)
    (hEv : ∀ ψ : Name → Nat, mp.base2.acval eqName ψ = eqValAV ψ)
    (hfresh : env.find? eqReflA.name = none)
    (hwf : EnvWF ⟨eqReflA :: env.consts⟩) :
    ∃ mp' : EnvModelM V μ ⟨eqReflA :: env.consts⟩,
      mp'.base2.acval
        = acvalWith mp.base2.acval eqReflA.name eqReflValAV := by
  have hty := fun ψ =>
    denoteMeta_eqReflTy (m := mp.base2) (A := eqReflValAV) (c₀ := eqReflA)
      ψ (by decide) hE hEv
  refine declStep_preserves_of_basis_cons mp (A := eqReflValAV) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf
      (fun ψ => by rw [eqReflValAV_erase ψ]; exact eqReflValT_closed ψ)
      rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT eqReflA.name ψ
          = none from rfl] at hp
        exact nomatch hp)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le k)
        (by rw [eqReflValAV_erase]; exact eqReflValT_closed ψ)) 1)
    (fun ψ₁ ψ₂ hp => eqReflValAV_congr
      (hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)))
    (fun ψ ρ => eqReflValAV_wellDenoted ψ ρ)
    (fun ψ ρ => eqReflValAV_validV ψ ρ)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (eqReflTy_data ψ ρ).1
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [(eqReflTy_data ψ ρ).2]
    exact eqReflValAV_mem ψ ρ

/-! ## `Eq.rec`

Its six binders are pinned `.ifAllZero [u_1]` — the *motive* level's
zero test, not the type's — so the whole constant lives at one bit `b`
with `b = 0 ↔ ψ u_1 = 0`.  Its rule returns the minor premise, so the
only real content anywhere in the block is that the major premise's
membership forces `a = b` and the proof to be `pt`: an inhabitant of
`eqv a b` gives `a = b` by `mem_eqv`, and `eqv` is a truth value, so
the inhabitant is the canonical proof by `mem_univ_zero`.

`eqRecValAV`'s membership and grading are the two items the ENDGAME E
seal recorded as owed; both are below. -/

/-- `Eq.rec`'s motive binder domain reading. -/
def eqRecMotiveTy (ψ : Name → Nat) : AnnotTerm :=
  .pi 0 1 (.bvar 1) (.pi 0 1 (eqSpine ψ 2 1 0) (.sort (ψ u1N)))

/-- `Eq.rec`'s minor binder domain reading. -/
def eqRecMinorTy (ψ : Name → Nat) : AnnotTerm :=
  .app (.app (.bvar 0) (.bvar 1)) (eqReflSpine ψ 2 1)

/-- `Eq.rec`'s type reading. -/
def eqRecTy (b : Nat) (ψ : Name → Nat) : AnnotTerm :=
  .pi 0 b (.sort (ψ uN))
    (.pi 0 b (.bvar 0)
      (.pi 0 b (eqRecMotiveTy ψ)
        (.pi 0 b (eqRecMinorTy ψ)
          (.pi 0 b (.bvar 3)
            (.pi 0 b (eqSpine ψ 4 3 0)
              (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))))

/-- `Eq.rec`'s rule's RHS reading: the same four domains, over the
minor premise. -/
def eqRecRa (b : Nat) (ψ : Name → Nat) : AnnotTerm :=
  .lam b (.sort (ψ uN))
    (.lam b (.bvar 0)
      (.lam b (eqRecMotiveTy ψ)
        (.lam b (eqRecMinorTy ψ) (.bvar 0))))

/-- The motive space: `∀ b, a = b → Sort u₁`. -/
noncomputable def eqRecMotiveSpace (V : Type w) [SetTheory V]
    (u1 : Nat) (Aset a : V) : V :=
  piR 1 Aset fun b => piR 1 (eqv a b) fun _ => (univ u1 : V)

theorem eqRecMotiveTy_data {ψ : Name → Nat} {Aset a : V}
    (ρ : Nat → V) (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset) :
    interp V (cons a (cons Aset ρ)) (eqRecMotiveTy ψ)
        = eqRecMotiveSpace V (ψ u1N) Aset a ∧
      WellDenotedV V (cons a (cons Aset ρ)) (eqRecMotiveTy ψ) := by
  have hsp : ∀ b : V, b ∈ˢ Aset →
      interp V (cons b (cons a (cons Aset ρ))) (eqSpine ψ 2 1 0)
          = eqv a b ∧
        WellDenotedV V (cons b (cons a (cons Aset ρ))) (eqSpine ψ 2 1 0) ∧
        interp V (cons b (cons a (cons Aset ρ))) (eqSpine ψ 2 1 0)
          ∈ˢ (univZero : V) := fun b hb =>
    eqSpine_interp (ρ := cons b (cons a (cons Aset ρ)))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA ha hb
  have hdom : interp V (cons a (cons Aset ρ)) (AnnotTerm.bvar 1)
      = Aset := by simp [interp_bvar, cons]
  refine ⟨?_, ?_⟩
  · rw [eqRecMotiveTy, interp_pi, eqRecMotiveSpace, hdom]
    refine piR_congr fun b hb => ?_
    rw [interp_pi, (hsp b hb).1]
    exact piR_congr fun _ _ => interp_sort V _ _
  · refine ⟨⟨trivial, fun b hb => ?_⟩,
      ⟨trivial, fun b hb => ?_, fun h => absurd h Nat.one_ne_zero⟩⟩
    · rw [hdom] at hb
      exact ⟨(hsp b hb).2.1.1, fun _ _ => trivial⟩
    · rw [hdom] at hb
      exact ⟨(hsp b hb).2.1.2, fun _ _ => trivial,
        fun h => absurd h Nat.one_ne_zero⟩

theorem eqRecMinorTy_data {ψ : Name → Nat} {Aset a M : V}
    (ρ : Nat → V) (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset)
    (hM : M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a) :
    interp V (cons M (cons a (cons Aset ρ))) (eqRecMinorTy ψ)
        = app (app M a) pt ∧
      WellDenotedV V (cons M (cons a (cons Aset ρ))) (eqRecMinorTy ψ) ∧
      app (app M a) pt ∈ˢ (univ (ψ u1N) : V) := by
  obtain ⟨hrint, hrok⟩ := eqReflSpine_data (ψ := ψ) (i := 2) (j := 1)
    (ρ := cons M (cons a (cons Aset ρ)))
    (by simp [cons]) (by simp [cons]) hA ha
  have hM0 : M ∈ˢ piR 1 Aset (fun b => piR 1 (eqv a b)
      fun _ => (univ (ψ u1N) : V)) := hM
  have hMa : app M a ∈ˢ piR 1 (eqv a a) fun _ => (univ (ψ u1N) : V) :=
    app_mem_piR_pos Nat.one_ne_zero hM0 ha
  have hMap : app (app M a) pt ∈ˢ (univ (ψ u1N) : V) :=
    app_mem_piR_pos Nat.one_ne_zero hMa (pt_mem_eqv_self a)
  have hMb : interp V (cons M (cons a (cons Aset ρ)))
      (AnnotTerm.bvar 0) = M := by simp [interp_bvar, cons]
  have hab : interp V (cons M (cons a (cons Aset ρ)))
      (AnnotTerm.bvar 1) = a := by simp [interp_bvar, cons]
  refine ⟨?_, ⟨?_, ?_⟩, hMap⟩
  · rw [eqRecMinorTy, interp_app, interp_app, hrint, hMb, hab]
  · rw [eqRecMinorTy, WellDenoted_app]
    refine ⟨?_, hrok.1, 1, eqv a a, fun _ => (univ (ψ u1N) : V), ?_,
      by rw [hrint]; exact pt_mem_eqv_self a,
      fun h => absurd h Nat.one_ne_zero⟩
    · rw [WellDenoted_app]
      exact ⟨trivial, trivial, 1, Aset,
        fun b => piR 1 (eqv a b) fun _ => (univ (ψ u1N) : V),
        by rw [hMb]; exact hM0, by rw [hab]; exact ha,
        fun h => absurd h Nat.one_ne_zero⟩
    · rw [interp_app, hMb, hab]; exact hMa
  · exact ⟨⟨trivial, trivial⟩, hrok.2⟩

/-- **The major premise collapses the block**: an inhabitant of
`eqv a b` identifies `a` with `b` and is itself the canonical proof.
This is `Eq.rec`'s entire iota content, and it is why the layer does
not carry the constant at all (`eqRec_derivable`). -/
theorem eqRec_major_collapse {a b h : V} (hh : h ∈ˢ eqv a b) :
    a = b ∧ h = pt :=
  ⟨mem_eqv hh, mem_univ_zero (univ_zero (V := V) ▸ eqv_mem_univZero a b) hh⟩

/-! ### The tower, bit-cleaned

`eqRecValAV` carries the *type's* result sort `ψ u_1 + 1` at the
motive domain's inner binder where the reading carries `pwBit … .never
= 1`.  The two agree on zero-ness and on nothing else is read, so they
are `BitAgree` — which is the whole distance between the tower the
ENDGAME E seal built and the tower this block's walk wants. -/

/-- The tower with the reading's own numerals. -/
def eqRecRaTower (b : Nat) (ψ : Name → Nat) : AnnotTerm :=
  .lam b (.sort (ψ uN))
    (.lam b (.bvar 0)
      (.lam b (eqRecMotiveTy ψ)
        (.lam b (eqRecMinorTy ψ)
          (.lam b (.bvar 3)
            (.lam b (eqSpine ψ 4 3 0) (.bvar 2))))))

theorem bitAgree_eqRecValAV (ψ : Name → Nat) :
    AnnotTerm.BitAgree (eqRecRaTower (pwBit ψ (.ifAllZero [u1N])) ψ)
      (eqRecValAV ψ) :=
  .lam Iff.rfl (.sort _)
    (.lam Iff.rfl (.bvar 0)
      (.lam Iff.rfl
        (.pi Iff.rfl (.bvar 1)
          (.pi (Iff.intro (fun h => absurd h Nat.one_ne_zero)
              (fun h => absurd h (Nat.succ_ne_zero _)))
            (AnnotTerm.BitAgree.refl _) (.sort _)))
        (.lam Iff.rfl (AnnotTerm.BitAgree.refl _)
          (.lam Iff.rfl (.bvar 3)
            (.lam Iff.rfl (AnnotTerm.BitAgree.refl _) (.bvar 2))))))

/-- **`Eq.rec`'s tower is graded and inhabits its type's reading** —
the two items the ENDGAME E seal recorded as owed, taken in one walk
(`WellDenotedV_lam_mem` six times).  The only content is at the bottom:
the major premise collapses `b` onto `a` and itself onto `pt`, and the
minor premise is already there. -/
theorem eqRecRaTower_data {b : Nat} (ψ : Name → Nat)
    (hz : b = 0 ↔ ψ u1N = 0) (ρ : Nat → V) :
    WellDenotedV V ρ (eqRecRaTower b ψ) ∧
      interp V ρ (eqRecRaTower b ψ)
        ∈ˢ interp V ρ (eqRecTy b ψ) := by
  have hzero : ∀ x : V, x ∈ˢ (univ (ψ u1N) : V) → b = 0 →
      x ∈ˢ (univZero : V) := fun x hx hb => by
    rw [← univ_zero, ← hz.mp hb]; exact hx
  -- level 6: the body, at a fixed major premise
  have h6 : ∀ Aset a M mn bb : V, Aset ∈ˢ (univ (ψ uN) : V) →
      a ∈ˢ Aset → M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      mn ∈ˢ app (app M a) pt → bb ∈ˢ Aset →
      WellDenotedV V (cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
          (.lam b (eqSpine ψ 4 3 0) (.bvar 2)) ∧
        interp V (cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
            (.lam b (eqSpine ψ 4 3 0) (.bvar 2))
          ∈ˢ piR b (eqv a bb) (fun h => app (app M bb) h) := by
    intro Aset a M mn bb hA ha hM hmn hbb
    obtain ⟨hsint, hsok, -⟩ := eqSpine_interp
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
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := eqSpine ψ 4 3 0) (bd := .bvar 2)
      (F := fun h => app (app M bb) h) hsok
      (fun h hh => by
        rw [hsint] at hh
        refine ⟨⟨trivial, trivial⟩, ?_⟩
        rw [show interp V (cons h (cons bb (cons mn (cons M
            (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 2) = mn
          from by simp [interp_bvar, cons], (key h hh).1]
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
      WellDenotedV V (cons mn (cons M (cons a (cons Aset ρ))))
          (.lam b (.bvar 3) (.lam b (eqSpine ψ 4 3 0) (.bvar 2))) ∧
        interp V (cons mn (cons M (cons a (cons Aset ρ))))
            (.lam b (.bvar 3) (.lam b (eqSpine ψ 4 3 0) (.bvar 2)))
          ∈ˢ piR b Aset
            (fun bb => piR b (eqv a bb) fun h => app (app M bb) h) := by
    intro Aset a M mn hA ha hM hmn
    have hdom : interp V (cons mn (cons M (cons a (cons Aset ρ))))
        (AnnotTerm.bvar 3) = Aset := by simp [interp_bvar, cons]
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := AnnotTerm.bvar 3)
      (bd := .lam b (eqSpine ψ 4 3 0) (.bvar 2))
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
      WellDenotedV V (cons M (cons a (cons Aset ρ)))
          (.lam b (eqRecMinorTy ψ)
            (.lam b (.bvar 3)
              (.lam b (eqSpine ψ 4 3 0) (.bvar 2)))) ∧
        interp V (cons M (cons a (cons Aset ρ)))
            (.lam b (eqRecMinorTy ψ)
              (.lam b (.bvar 3)
                (.lam b (eqSpine ψ 4 3 0) (.bvar 2))))
          ∈ˢ piR b (app (app M a) pt) (fun _ => piR b Aset
            (fun bb => piR b (eqv a bb) fun h => app (app M bb) h)) := by
    intro Aset a M hA ha hM
    obtain ⟨hmint, hmok, -⟩ := eqRecMinorTy_data ρ hA ha hM
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := eqRecMinorTy ψ)
      (F := fun _ => piR b Aset
        (fun bb => piR b (eqv a bb) fun h => app (app M bb) h))
      hmok
      (fun mn hmn => h5 Aset a M mn hA ha hM (by rwa [hmint] at hmn))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hmint] at hstep
    exact hstep
  -- level 3
  have h3 : ∀ Aset a : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      WellDenotedV V (cons a (cons Aset ρ))
          (.lam b (eqRecMotiveTy ψ)
            (.lam b (eqRecMinorTy ψ)
              (.lam b (.bvar 3)
                (.lam b (eqSpine ψ 4 3 0) (.bvar 2))))) ∧
        interp V (cons a (cons Aset ρ))
            (.lam b (eqRecMotiveTy ψ)
              (.lam b (eqRecMinorTy ψ)
                (.lam b (.bvar 3)
                  (.lam b (eqSpine ψ 4 3 0) (.bvar 2)))))
          ∈ˢ piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
            (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
              (fun bb => piR b (eqv a bb)
                fun h => app (app M bb) h))) := by
    intro Aset a hA ha
    obtain ⟨hmint, hmok⟩ := eqRecMotiveTy_data ρ hA ha
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := eqRecMotiveTy ψ)
      (F := fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
        (fun bb => piR b (eqv a bb) fun h => app (app M bb) h)))
      hmok
      (fun M hM => h4 Aset a M hA ha (by rwa [hmint] at hM))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hmint] at hstep
    exact hstep
  -- level 2
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ (ψ uN) : V) →
      WellDenotedV V (cons Aset ρ)
          (.lam b (.bvar 0)
            (.lam b (eqRecMotiveTy ψ)
              (.lam b (eqRecMinorTy ψ)
                (.lam b (.bvar 3)
                  (.lam b (eqSpine ψ 4 3 0) (.bvar 2)))))) ∧
        interp V (cons Aset ρ)
            (.lam b (.bvar 0)
              (.lam b (eqRecMotiveTy ψ)
                (.lam b (eqRecMinorTy ψ)
                  (.lam b (.bvar 3)
                    (.lam b (eqSpine ψ 4 3 0) (.bvar 2))))))
          ∈ˢ piR b Aset (fun a =>
            piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
              (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
                (fun bb => piR b (eqv a bb)
                  fun h => app (app M bb) h)))) := by
    intro Aset hA
    have hdom : interp V (cons Aset ρ) (AnnotTerm.bvar 0) = Aset := by
      simp [interp_bvar, cons]
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := AnnotTerm.bvar 0)
      (F := fun a => piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
          (fun bb => piR b (eqv a bb) fun h => app (app M bb) h))))
      ⟨trivial, trivial⟩
      (fun a ha => h3 Aset a hA (by rwa [hdom] at ha))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hdom] at hstep
    exact hstep
  have hstep := WellDenotedV_lam_mem (V := V) (b := b)
    (Aa := .sort (ψ uN))
    (F := fun Aset => piR b Aset (fun a =>
      piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
          (fun bb => piR b (eqv a bb) fun h => app (app M bb) h)))))
    ⟨trivial, trivial⟩
    (fun Aset hA => h2 Aset (by rwa [interp_sort] at hA))
    (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
  refine ⟨hstep.1, ?_⟩
  rw [interp_sort] at hstep
  refine (?_ : interp V ρ (eqRecTy b ψ)
    = piR b (univ (ψ uN) : V) (fun Aset => piR b Aset (fun a =>
      piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt) (fun _ => piR b Aset
          (fun bb => piR b (eqv a bb)
            fun h => app (app M bb) h)))))) ▸ hstep.2
  -- the type reading's own six products, in the same order
  rw [eqRecTy, interp_pi, interp_sort]
  refine piR_congr fun Aset hAset => ?_
  rw [interp_pi]
  simp only [interp_bvar, cons]
  refine piR_congr fun a ha => ?_
  rw [interp_pi, (eqRecMotiveTy_data ρ hAset ha).1]
  refine piR_congr fun M hM => ?_
  rw [interp_pi, (eqRecMinorTy_data ρ hAset ha hM).1]
  refine piR_congr fun mn _ => ?_
  rw [interp_pi]
  simp only [interp_bvar, cons]
  refine piR_congr fun bb hbb => ?_
  rw [interp_pi,
    (eqSpine_interp (ρ := cons bb (cons mn (cons M (cons a
        (cons Aset ρ))))) (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons])
      hAset ha hbb).1]
  refine piR_congr fun h _ => ?_
  simp [interp_app, interp_bvar, cons]

/-! ### The two readings -/

/-- **`Eq.rec`'s type reading.** -/
theorem denoteMeta_eqRecA_type (ψ : Name → Nat)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValAV ψ)
    (hRv : ∀ ψ : Name → Nat, m.acval eqReflName ψ = eqReflValAV ψ) :
    denoteMeta (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ 0 eqRecA.toConstantVal.type
      = some (eqRecTy (pwBit ψ (.ifAllZero [u1N])) ψ) := by
  have hEc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ d (.const eqName [.param uN])
        = some (eqValAV ψ) := by
    intro d
    rw [denoteMeta_eqLeaf (m := m) (A := A) ψ (Level.param uN)
        (by decide) hE d,
      show ([Level.param uN] : List Level)
        = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN], hEv]
  have hRc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ d (.const eqReflName [.param uN])
        = some (eqReflValAV ψ) := by
    intro d
    have hf' : (⟨eqRecA :: env.consts⟩ : Env).find? eqReflName
        = some eqReflA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hR
    rw [denoteMeta_const hf' (by rfl), acvalWith_ne (by decide),
      show Level.substFn ψ eqReflA.toConstantVal.levelParams
        [Level.param uN] = Level.substFn ψ [uN]
          (List.map Level.param [uN]) from rfl,
      Level.substFn_param_self ψ [uN], hRv]
  rw [show eqRecA.toConstantVal.type
      = Expr.forallE (.sort (.param uN))
          (Expr.forallE (.bvar 0)
            (Expr.forallE
              (Expr.forallE (.bvar 1)
                (Expr.forallE
                  (.app (.app (.app (.const eqName [.param uN])
                    (.bvar 2)) (.bvar 1)) (.bvar 0))
                  (.sort (.param u1N))
                  { pw := .never })
                { pw := .never })
              (Expr.forallE
                (.app (.app (.bvar 0) (.bvar 1))
                  (.app (.app (.const eqReflName [.param uN])
                    (.bvar 2)) (.bvar 1)))
                (Expr.forallE (.bvar 3)
                  (Expr.forallE
                    (.app (.app (.app (.const eqName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 0))
                    (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
                    { pw := .ifAllZero [u1N] })
                  { pw := .ifAllZero [u1N] })
                { pw := .ifAllZero [u1N] })
              { pw := .ifAllZero [u1N] })
            { pw := .ifAllZero [u1N] })
          { pw := .ifAllZero [u1N] } from rfl]
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
    Expr.instantiate1, eqRecTy, eqRecMotiveTy, eqRecMinorTy,
    eqSpine, eqReflSpine, pwBit_never, hEc, hRc, Level.eval]

/-- **`Eq.rec`'s rule's RHS reading.** -/
theorem denoteMeta_eqRec_rhs (ψ : Name → Nat)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValAV ψ)
    (hRv : ∀ ψ : Name → Nat, m.acval eqReflName ψ = eqReflValAV ψ) :
    denoteMeta (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ 0 eqRecRule.rhs
      = some (eqRecRa (pwBit ψ (.ifAllZero [u1N])) ψ) := by
  have hEc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ d (.const eqName [.param uN])
        = some (eqValAV ψ) := by
    intro d
    rw [denoteMeta_eqLeaf (m := m) (A := A) ψ (Level.param uN)
        (by decide) hE d,
      show ([Level.param uN] : List Level)
        = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN], hEv]
  have hRc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts⟩ ψ d (.const eqReflName [.param uN])
        = some (eqReflValAV ψ) := by
    intro d
    have hf' : (⟨eqRecA :: env.consts⟩ : Env).find? eqReflName
        = some eqReflA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hR
    rw [denoteMeta_const hf' (by rfl), acvalWith_ne (by decide),
      show Level.substFn ψ eqReflA.toConstantVal.levelParams
        [Level.param uN] = Level.substFn ψ [uN]
          (List.map Level.param [uN]) from rfl,
      Level.substFn_param_self ψ [uN], hRv]
  simp only [eqRecRule]
  simp [denoteMeta_lam, denoteMeta_forallE, denoteMeta_sort, denoteMeta_app,
    denoteMeta_fvar, Expr.instantiate1, eqRecRa, eqRecMotiveTy,
    eqRecMinorTy, eqSpine, eqReflSpine, pwBit_never, hEc, hRc,
    Level.eval]

/-! ### The RHS tower and the two firing sides -/

/-- The product the RHS tower inhabits. -/
noncomputable def eqRecRaSpace (V : Type w) [SetTheory V]
    (b u u1 : Nat) : V :=
  piR b (univ u : V) fun Aset => piR b Aset fun a =>
    piR b (eqRecMotiveSpace V u1 Aset a) fun M =>
      piR b (app (app M a) pt) fun _ => app (app M a) pt

theorem eqRecRa_data {b : Nat} (ψ : Name → Nat)
    (hz : b = 0 ↔ ψ u1N = 0) (ρ : Nat → V) :
    WellDenotedV V ρ (eqRecRa b ψ) ∧
      interp V ρ (eqRecRa b ψ)
        ∈ˢ eqRecRaSpace V b (ψ uN) (ψ u1N) := by
  have hzero : ∀ x : V, x ∈ˢ (univ (ψ u1N) : V) → b = 0 →
      x ∈ˢ (univZero : V) := fun x hx hb => by
    rw [← univ_zero, ← hz.mp hb]; exact hx
  have h4 : ∀ Aset a M : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      WellDenotedV V (cons M (cons a (cons Aset ρ)))
          (.lam b (eqRecMinorTy ψ) (.bvar 0)) ∧
        interp V (cons M (cons a (cons Aset ρ)))
            (.lam b (eqRecMinorTy ψ) (.bvar 0))
          ∈ˢ piR b (app (app M a) pt) (fun _ => app (app M a) pt) := by
    intro Aset a M hA ha hM
    obtain ⟨hmint, hmok, hmuniv⟩ := eqRecMinorTy_data ρ hA ha hM
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := eqRecMinorTy ψ) (bd := .bvar 0)
      (F := fun _ => app (app M a) pt) hmok
      (fun mn hmn => by
        rw [hmint] at hmn
        exact ⟨⟨trivial, trivial⟩, by
          rw [show interp V (cons mn (cons M (cons a (cons Aset ρ))))
            (AnnotTerm.bvar 0) = mn from by simp [interp_bvar, cons]]
          exact hmn⟩)
      (fun hb _ _ => hzero _ hmuniv hb)
    rw [hmint] at hstep
    exact hstep
  have h3 : ∀ Aset a : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      WellDenotedV V (cons a (cons Aset ρ))
          (.lam b (eqRecMotiveTy ψ)
            (.lam b (eqRecMinorTy ψ) (.bvar 0))) ∧
        interp V (cons a (cons Aset ρ))
            (.lam b (eqRecMotiveTy ψ)
              (.lam b (eqRecMinorTy ψ) (.bvar 0)))
          ∈ˢ piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
            (fun M => piR b (app (app M a) pt)
              (fun _ => app (app M a) pt)) := by
    intro Aset a hA ha
    obtain ⟨hmint, hmok⟩ := eqRecMotiveTy_data ρ hA ha
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := eqRecMotiveTy ψ)
      (F := fun M => piR b (app (app M a) pt)
        (fun _ => app (app M a) pt)) hmok
      (fun M hM => h4 Aset a M hA ha (by rwa [hmint] at hM))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hmint] at hstep
    exact hstep
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ (ψ uN) : V) →
      WellDenotedV V (cons Aset ρ)
          (.lam b (.bvar 0) (.lam b (eqRecMotiveTy ψ)
            (.lam b (eqRecMinorTy ψ) (.bvar 0)))) ∧
        interp V (cons Aset ρ)
            (.lam b (.bvar 0) (.lam b (eqRecMotiveTy ψ)
              (.lam b (eqRecMinorTy ψ) (.bvar 0))))
          ∈ˢ piR b Aset (fun a =>
            piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
              (fun M => piR b (app (app M a) pt)
                (fun _ => app (app M a) pt))) := by
    intro Aset hA
    have hdom : interp V (cons Aset ρ) (AnnotTerm.bvar 0) = Aset := by
      simp [interp_bvar, cons]
    have hstep := WellDenotedV_lam_mem (V := V) (b := b)
      (Aa := AnnotTerm.bvar 0)
      (F := fun a => piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt)
          (fun _ => app (app M a) pt)))
      ⟨trivial, trivial⟩
      (fun a ha => h3 Aset a hA (by rwa [hdom] at ha))
      (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
    rw [hdom] at hstep
    exact hstep
  have hstep := WellDenotedV_lam_mem (V := V) (b := b)
    (Aa := .sort (ψ uN))
    (F := fun Aset => piR b Aset (fun a =>
      piR b (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piR b (app (app M a) pt)
          (fun _ => app (app M a) pt))))
    ⟨trivial, trivial⟩
    (fun Aset hA => h2 Aset (by rwa [interp_sort] at hA))
    (fun hb _ _ => by rw [hb]; exact piR_zero_mem_univZero)
  rw [interp_sort] at hstep
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
        (interp V ρ (eqRecRaTower b ψ)) Aset) a) M) mn) bb) h = mn := by
  obtain ⟨hmint, -, hmuniv⟩ := eqRecMinorTy_data ρ hA ha hM
  by_cases hb : b = 0
  · rw [eqRecRaTower, interp_lam, hb, lamR_zero, app_pt, app_pt,
      app_pt, app_pt, app_pt, app_pt]
    have h0 : app (app M a) pt ∈ˢ (univ 0 : V) := by
      rw [← hz.mp hb]; exact hmuniv
    exact (mem_univ_zero h0 hmn).symm
  · obtain ⟨hmoint, -⟩ := eqRecMotiveTy_data ρ hA ha
    obtain ⟨hsint, -, -⟩ := eqSpine_interp
      (ρ := cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
      (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA ha hbb
    rw [eqRecRaTower, interp_lam, interp_sort, app_lamR_pos hb hA,
      interp_lam,
      show interp V (cons Aset ρ) (AnnotTerm.bvar 0) = Aset
        from by simp [interp_bvar, cons],
      app_lamR_pos hb ha,
      interp_lam, hmoint, app_lamR_pos hb hM,
      interp_lam, hmint, app_lamR_pos hb hmn,
      interp_lam,
      show interp V (cons mn (cons M (cons a (cons Aset ρ))))
        (AnnotTerm.bvar 3) = Aset from by simp [interp_bvar, cons],
      app_lamR_pos hb hbb,
      interp_lam, hsint, app_lamR_pos hb hh]
    simp [interp_bvar, cons]

/-- …and the RHS tower's four-fold application is the same value. -/
theorem eqRecRa_app₄ {b : Nat} (ψ : Name → Nat)
    (hz : b = 0 ↔ ψ u1N = 0) (ρ : Nat → V) {Aset a M mn : V}
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset)
    (hM : M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a)
    (hmn : mn ∈ˢ app (app M a) pt) :
    app (app (app (app (interp V ρ (eqRecRa b ψ)) Aset) a) M) mn
      = mn := by
  obtain ⟨hmint, -, hmuniv⟩ := eqRecMinorTy_data ρ hA ha hM
  by_cases hb : b = 0
  · rw [eqRecRa, interp_lam, hb, lamR_zero, app_pt, app_pt, app_pt,
      app_pt]
    have h0 : app (app M a) pt ∈ˢ (univ 0 : V) := by
      rw [← hz.mp hb]; exact hmuniv
    exact (mem_univ_zero h0 hmn).symm
  · obtain ⟨hmoint, -⟩ := eqRecMotiveTy_data ρ hA ha
    rw [eqRecRa, interp_lam, interp_sort, app_lamR_pos hb hA,
      interp_lam,
      show interp V (cons Aset ρ) (AnnotTerm.bvar 0) = Aset
        from by simp [interp_bvar, cons],
      app_lamR_pos hb ha,
      interp_lam, hmoint, app_lamR_pos hb hM,
      interp_lam, hmint, app_lamR_pos hb hmn]
    simp [interp_bvar, cons]

/-! ### The row -/

theorem eqRecValAV_congr {ψ₁ ψ₂ : Name → Nat} (hu : ψ₁ uN = ψ₂ uN)
    (hu1 : ψ₁ u1N = ψ₂ u1N) : eqRecValAV ψ₁ = eqRecValAV ψ₂ := by
  have hb : pwBit ψ₁ (ConLeche.PropWhen.ifAllZero [u1N])
      = pwBit ψ₂ (ConLeche.PropWhen.ifAllZero [u1N]) := by
    unfold pwBit
    simp [hu1]
  rw [eqRecValAV, eqRecValAV, hb, hu, hu1, eqValAV_congr hu,
    eqReflValAV_congr hu]

set_option maxHeartbeats 1000000 in
/-- **`Eq.rec`'s `RecRuleLaw` row.**  The rule is `.plain`, so both
`.nested` conjuncts are `nomatch`; the fired equality is the minor
premise on both sides (`eqRecRaTower_app₆` against `eqRecRa_app₄`),
and the transport is four `WellDenotedV_app_of` steps. -/
theorem eqRecLaw {m : EnvModel V env}
    (m₂ : EnvModel V ⟨eqRecA :: env.consts⟩)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValAV ψ)
    (hRv : ∀ ψ : Name → Nat, m.acval eqReflName ψ = eqReflValAV ψ)
    (hac : m₂.acval = acvalWith m.acval eqRecA.name eqRecValAV)
    (φ : Name → Nat) :
    RecRuleLaw m₂ φ eqRecA.name eqRecA.toConstantVal 5 4
      eqRecRule := by
  refine ⟨by decide, fun us hus => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ eqRecA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  have hz : pwBit ψ (ConLeche.PropWhen.ifAllZero [u1N]) = 0 ↔ ψ u1N = 0 :=
    pwBit_ifAllZero_single ψ u1N
  have hRa : denoteMeta m₂.acval ⟨eqRecA :: env.consts⟩ φ 0
      (eqRecRule.rhs.instantiateLevelParams
        eqRecA.toConstantVal.levelParams us)
      = some (eqRecRa (pwBit ψ (.ifAllZero [u1N])) ψ) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteMeta_eqRec_rhs (m := m) _ hE hR hEv hRv]
  refine ⟨_, hRa, fun ρ => (eqRecRa_data ψ hz ρ).1, ?_, ?_⟩
  · intro _ _ h
    exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev _ hnested hpin hTVa hTVja hfitR hfitC
  have hR' : (⟨eqRecA :: env.consts⟩ : Env).find? eqReflName
      = some eqReflA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hR
  rw [show RecRule.ctor eqRecRule = eqReflName from rfl, hR'] at hfj
  obtain ⟨rfl, rfl, rfl⟩ :
      cvj = eqReflA.toConstantVal ∧ cnP = 2 ∧ cnF = 0 := by
    injection Option.some.inj hfj with a1 a2 a3
    exact ⟨a1.symm, a2.symm, a3.symm⟩
  obtain ⟨x1, x2, x3, x4, x5, rfl⟩ :
      ∃ p q r s t, xs = [p, q, r, s, t] := by
    match xs, hxs with
    | [p, q, r, s, t], _ => exact ⟨p, q, r, s, t, rfl⟩
  obtain ⟨y1, y2, rfl⟩ : ∃ p q, ys = [p, q] := by
    match ys, hys with
    | [p, q], _ => exact ⟨p, q, rfl⟩
  have hulev : Level.substFn φ eqReflA.toConstantVal.levelParams usj uN
      = ψ uN := by
    rw [congrFun hlev uN, hψ]
    show Level.eval φ (Level.subst eqRecA.toConstantVal.levelParams
      us (.param uN)) = _
    rw [Level.subst, Level.eval_subst_go]
  have hTyRead : denoteMeta m₂.acval ⟨eqRecA :: env.consts⟩ φ 0
      (eqRecA.toConstantVal.type.instantiateLevelParams
        eqRecA.toConstantVal.levelParams us)
      = some (eqRecTy (pwBit ψ (.ifAllZero [u1N])) ψ) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteMeta_eqRecA_type (m := m) _ hE hR hEv hRv]
  obtain rfl : TVa = _ :=
    (Option.some.inj (hTyRead.symm.trans hTVa)).symm
  have hCtorRead : denoteMeta m₂.acval ⟨eqRecA :: env.consts⟩ φ 0
      (eqReflA.toConstantVal.type.instantiateLevelParams
        eqReflA.toConstantVal.levelParams usj)
      = some (eqReflTy
          (Level.substFn φ eqReflA.toConstantVal.levelParams usj)) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac,
      denoteMeta_eqReflTy (m := m) _ (by decide) hE hEv]
  obtain rfl : TVja = _ :=
    (Option.some.inj (hCtorRead.symm.trans hTVja)).symm
  rw [eqRecTy] at hfitR
  cases hfitR with | cons f1 hfitR =>
  cases hfitR with | cons f2 hfitR =>
  cases hfitR with | cons f3 hfitR =>
  cases hfitR with | cons f4 hfitR =>
  cases hfitR with | cons f5 hfitR =>
  cases hfitR with | cons f6 _ =>
  rw [interp_sort] at f1
  rw [interp_inst0] at f2
  simp only [interp_bvar, cons] at f2
  rw [interp_inst0, interp_inst_cons1,
    (eqRecMotiveTy_data ρ f1 f2).1] at f3
  rw [interp_inst0, interp_inst_cons1, interp_inst_cons2,
    (eqRecMinorTy_data ρ f1 f2 f3).1] at f4
  rw [interp_inst0, interp_inst_cons1, interp_inst_cons2,
    interp_inst_cons3] at f5
  simp only [interp_bvar, cons] at f5
  rw [interp_inst0, interp_inst_cons1, interp_inst_cons2,
    interp_inst_cons3, interp_inst_cons4,
    (eqSpine_interp (ρ := cons (interp V ρ x5) (cons (interp V ρ x4)
        (cons (interp V ρ x3) (cons (interp V ρ x2)
          (cons (interp V ρ x1) ρ))))) (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons])
      f1 f2 f5).1] at f6
  rw [eqReflTy] at hfitC
  cases hfitC with | cons g1 hfitC =>
  cases hfitC with | cons g2 _ =>
  rw [hulev, interp_sort] at g1
  rw [interp_inst0] at g2
  simp only [interp_bvar, cons] at g2
  have hrecL : m₂.acval eqRecA.name
      (Level.substFn φ eqRecA.toConstantVal.levelParams us)
      = eqRecValAV ψ := by
    rw [hac, acvalWith_self, hψ]
  have hctorL : m₂.acval eqReflName
      (Level.substFn φ eqReflA.toConstantVal.levelParams usj)
      = eqReflValAV
        (Level.substFn φ eqReflA.toConstantVal.levelParams usj) := by
    rw [hac, acvalWith_ne (by decide), hRv]
  simp only [show RecRule.ctor eqRecRule = eqReflName from rfl,
    AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil, interp_app, hctorL,
    eqReflValAV_interp, app_pt] at f6
  refine ⟨?_, ?_⟩
  · -- the fired equality
    simp only [show RecRule.ctor eqRecRule = eqReflName from rfl,
      show eqRecRule.ctorParams = 2 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      List.append_nil, AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil, hrecL,
      interp_app, hctorL, eqReflValAV_interp, app_pt]
    rw [← AnnotTerm.BitAgree.interp_eq V (bitAgree_eqRecValAV ψ) ρ,
      eqRecRaTower_app₆ ψ hz ρ f1 f2 f3 f4 f5 f6,
      eqRecRa_app₄ ψ hz ρ f1 f2 f3 f4]
  · -- the transport
    intro hxsA _
    simp only [show eqRecRule.ctorParams = 2 from rfl,
      List.take, List.drop, List.append_nil,
      AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil]
    have hRm := (eqRecRa_data ψ hz ρ).2
    rw [eqRecRaSpace] at hRm
    have h1 := WellDenotedV_app_of ((eqRecRa_data ψ hz ρ).1)
      (hxsA x1 (by simp)) hRm f1
      (fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero)
    have h2 := WellDenotedV_app_of h1.1 (hxsA x2 (by simp)) h1.2 f2
      (fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero)
    have h3 := WellDenotedV_app_of h2.1 (hxsA x3 (by simp)) h2.2 f3
      (fun hb0 _ _ => by rw [hb0]; exact piR_zero_mem_univZero)
    exact (WellDenotedV_app_of h3.1 (hxsA x4 (by simp)) h3.2 f4
      (fun hb0 _ _ => by
        rw [← univ_zero, ← hz.mp hb0]
        exact (eqRecMinorTy_data ρ f1 f2 f3).2.2)).1

/-- **`Eq.rec`'s type reading is graded** — six `WellDenotedV_pi_bit`
steps; the innermost body is the motive applied to the major premise,
whose fibre is a truth value exactly when the bit is zero. -/
theorem eqRecTy_wellDenotedV {b : Nat} (ψ : Name → Nat)
    (hz : b = 0 ↔ ψ u1N = 0) (ρ : Nat → V) :
    WellDenotedV V ρ (eqRecTy b ψ) := by
  have h6 : ∀ Aset a M mn bb : V, Aset ∈ˢ (univ (ψ uN) : V) →
      a ∈ˢ Aset → M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      bb ∈ˢ Aset →
      WellDenotedV V (cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
        (.pi 0 b (eqSpine ψ 4 3 0)
          (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))) := by
    intro Aset a M mn bb hA ha hM hbb
    obtain ⟨hsint, hsok, -⟩ := eqSpine_interp
      (ρ := cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
      (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA ha hbb
    have hM0 : M ∈ˢ piR 1 Aset (fun x => piR 1 (eqv a x)
        fun _ => (univ (ψ u1N) : V)) := hM
    have hMb : app M bb ∈ˢ piR 1 (eqv a bb)
        fun _ => (univ (ψ u1N) : V) :=
      app_mem_piR_pos Nat.one_ne_zero hM0 hbb
    refine WellDenotedV_pi_bit hsok (fun h hh => ?_) (fun hb h hh => ?_)
    · rw [hsint] at hh
      refine ⟨?_, ⟨⟨trivial, trivial⟩, trivial⟩⟩
      rw [WellDenoted_app]
      refine ⟨?_, trivial, 1, eqv a bb, fun _ => (univ (ψ u1N) : V),
        ?_, ?_, fun hx => absurd hx Nat.one_ne_zero⟩
      · rw [WellDenoted_app]
        refine ⟨trivial, trivial, 1, Aset,
          fun x => piR 1 (eqv a x) fun _ => (univ (ψ u1N) : V), ?_, ?_,
          fun hx => absurd hx Nat.one_ne_zero⟩
        · rw [show interp V (cons h (cons bb (cons mn (cons M
              (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 3) = M
            from by simp [interp_bvar, cons]]
          exact hM0
        · rw [show interp V (cons h (cons bb (cons mn (cons M
              (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 1) = bb
            from by simp [interp_bvar, cons]]
          exact hbb
      · rw [interp_app,
          show interp V (cons h (cons bb (cons mn (cons M
              (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 3) = M
            from by simp [interp_bvar, cons],
          show interp V (cons h (cons bb (cons mn (cons M
              (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 1) = bb
            from by simp [interp_bvar, cons]]
        exact hMb
      · rw [show interp V (cons h (cons bb (cons mn (cons M
            (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 0) = h
          from by simp [interp_bvar, cons]]
        exact hh
    · rw [hsint] at hh
      rw [interp_app, interp_app,
        show interp V (cons h (cons bb (cons mn (cons M
            (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 3) = M
          from by simp [interp_bvar, cons],
        show interp V (cons h (cons bb (cons mn (cons M
            (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 1) = bb
          from by simp [interp_bvar, cons],
        show interp V (cons h (cons bb (cons mn (cons M
            (cons a (cons Aset ρ)))))) (AnnotTerm.bvar 0) = h
          from by simp [interp_bvar, cons],
        ← univ_zero, ← hz.mp hb]
      exact app_mem_piR_pos Nat.one_ne_zero hMb hh
  have h5 : ∀ Aset a M mn : V, Aset ∈ˢ (univ (ψ uN) : V) →
      a ∈ˢ Aset → M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      WellDenotedV V (cons mn (cons M (cons a (cons Aset ρ))))
        (.pi 0 b (.bvar 3) (.pi 0 b (eqSpine ψ 4 3 0)
          (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))) := by
    intro Aset a M mn hA ha hM
    have hdom : interp V (cons mn (cons M (cons a (cons Aset ρ))))
        (AnnotTerm.bvar 3) = Aset := by simp [interp_bvar, cons]
    refine WellDenotedV_pi_bit (Aa := .bvar 3) ⟨trivial, trivial⟩
      (fun bb hbb => h6 Aset a M mn bb hA ha hM (by rwa [hdom] at hbb))
      (fun hb _ _ => by rw [interp_pi, hb]; exact piR_zero_mem_univZero)
  have h4 : ∀ Aset a M : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      WellDenotedV V (cons M (cons a (cons Aset ρ)))
        (.pi 0 b (eqRecMinorTy ψ)
          (.pi 0 b (.bvar 3) (.pi 0 b (eqSpine ψ 4 3 0)
            (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))) := by
    intro Aset a M hA ha hM
    obtain ⟨-, hmok, -⟩ := eqRecMinorTy_data ρ hA ha hM
    refine WellDenotedV_pi_bit hmok (fun mn _ => h5 Aset a M mn hA ha hM)
      (fun hb _ _ => by rw [interp_pi, hb]; exact piR_zero_mem_univZero)
  have h3 : ∀ Aset a : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      WellDenotedV V (cons a (cons Aset ρ))
        (.pi 0 b (eqRecMotiveTy ψ) (.pi 0 b (eqRecMinorTy ψ)
          (.pi 0 b (.bvar 3) (.pi 0 b (eqSpine ψ 4 3 0)
            (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))) := by
    intro Aset a hA ha
    obtain ⟨hmint, hmok⟩ := eqRecMotiveTy_data ρ hA ha
    refine WellDenotedV_pi_bit hmok
      (fun M hM => h4 Aset a M hA ha (by rwa [hmint] at hM))
      (fun hb _ _ => by rw [interp_pi, hb]; exact piR_zero_mem_univZero)
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ (ψ uN) : V) →
      WellDenotedV V (cons Aset ρ)
        (.pi 0 b (.bvar 0) (.pi 0 b (eqRecMotiveTy ψ)
          (.pi 0 b (eqRecMinorTy ψ)
            (.pi 0 b (.bvar 3) (.pi 0 b (eqSpine ψ 4 3 0)
              (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))))) := by
    intro Aset hA
    have hdom : interp V (cons Aset ρ) (AnnotTerm.bvar 0) = Aset := by
      simp [interp_bvar, cons]
    refine WellDenotedV_pi_bit (Aa := .bvar 0) ⟨trivial, trivial⟩
      (fun a ha => h3 Aset a hA (by rwa [hdom] at ha))
      (fun hb _ _ => by rw [interp_pi, hb]; exact piR_zero_mem_univZero)
  rw [eqRecTy]
  refine WellDenotedV_pi_bit (Aa := .sort (ψ uN)) ⟨trivial, trivial⟩
    (fun Aset hA => h2 Aset (by rwa [interp_sort] at hA))
    (fun hb _ _ => by rw [interp_pi, hb]; exact piR_zero_mem_univZero)

/-! ## The `Eq` block's representation (task #280): the constant functor whose fibre at the index `b` is the truth value of `a = b` -/

section EqRep
open ConLeche.SetTheory.Tower
open ConLeche (RecFieldKind IndCaps RecRule)

/-! ## The block's spelled pieces -/

/-- The first parameter variable of `Eq.refl`'s opened type. -/
@[expose] def eqFvAlpha : Expr := .fvar 0 (.sort (.param uN))

/-- The second parameter variable of `Eq.refl`'s opened type — and, as
the residual's only index argument, the block's index expression. -/
@[expose] def eqFvA : Expr := .fvar 1 eqFvAlpha

/-- The index telescope of `Eq`, at the parameter frame: the domain
`α`, which is the outer parameter variable. -/
@[expose] def eqIds : List AnnotTerm := [.bvar 1]

/-- `Eq.refl`'s index reading: the parameter `a`, at the
constructor's frame. -/
@[expose] def eqEs : List AnnotTerm := [.bvar 0]

/-- A bound variable is bounded at any strictly greater depth — the
readings' `DomsBelow`/`belowE` obligations, all of them numerals. -/
theorem bvarsBelow_bvarAV {k i : Nat} (h : i < k) :
    Term.bvarsBelow k (AnnotTerm.bvar i).erase := h

/-- **The `Eq` block's representation datum**: two parameters, one
index at sort `u`, one field-free constructor whose index expression
is the second parameter, and the fixpoint route's own functor. -/
@[expose] noncomputable def eqRepData (env₀ : Env) : IndRepData V where
  nP := 2
  nIdx := 1
  resSort := .zero
  isProp := (Level.isEquiv .zero .zero == some true)
  large := true
  elim := u1N
  env₀ := env₀
  ctorsA := [(eqReflA.toConstantVal, 0)]
  idxF := fun _ => [eqFvA]
  dsF := fun _ ψ => [(0, 0, .sort (ψ uN)), (0, 0, .bvar 0)]
  esF := fun _ _ => eqEs
  srcsF := fun _ => []
  ksF := fun _ => []
  fvsPF := fun _ => [eqFvAlpha, eqFvA]
  xFvsF := fun _ => []
  xrestF := fun _ => .app (.app (.app (.const eqName [.param uN]) eqFvAlpha) eqFvA) eqFvA
  eissF := fun _ _ => []
  essC := fun _ _ => eqEs
  eissC := fun _ _ => []
  tssF := fun _ _ => []
  k := 1
  nIdxs := [1]
  memberNames := [eqName]
  mems := fun _ => 0
  tgts := fun _ _ => 0
  ppsM := fun _ ψ => [(0, 1, .sort (ψ uN)), (0, 1, .bvar 0), (0, 1, .bvar 1)]
  lvlsM := fun _ ψ => [ψ uN + 1, ψ uN, ψ uN]
  IdsC := fun _ => eqIds
  u := fun ψ => ψ uN
  tup := fun ψ _ is => tupW (ψ uN) is
  Φ := fun ψ ρp => fixFunVI (ψ uN) 0 ρp eqIds 1 [[]] [[]] [[]] [[]] [eqEs]
  inj := fun _ _ _ => pt

section

variable {env₀ : Env}

/-- The datum's parameter-and-index telescope, reduced. -/
theorem eqRepData_pps (ψ : Name → Nat) :
    (eqRepData (V := V) env₀).ppsM 0 ψ
      = [(0, 1, .sort (ψ uN)), (0, 1, .bvar 0), (0, 1, .bvar 1)] := rfl

/-- `Eq.refl`'s binder data, reduced. -/
theorem eqRepData_dsF (j : Nat) (ψ : Name → Nat) :
    (eqRepData (V := V) env₀).dsF j ψ = [(0, 0, .sort (ψ uN)), (0, 0, .bvar 0)] := rfl

/-! ## The parameter frame -/

/-- A satisfying parameter frame gives the two parameters' memberships
(`α : Sort u` and `a : α`). -/
theorem eqRepData_frame {ψ : Name → Nat} {ρp : Nat → V}
    (hρ : Sat V ((eqRepData (V := V) env₀).params ψ).reverse ρp) :
    ρp 1 ∈ˢ (univ (ψ uN) : V) ∧ ρp 0 ∈ˢ ρp 1 := by
  have h1 := hρ 1 (.sort (ψ uN)) rfl
  have h0 := hρ 0 (.bvar 0) rfl
  rw [interp_sort] at h1
  rw [interp_bvar] at h0
  exact ⟨h1, h0⟩

/-- The index telescope is graded at a parameter frame. -/
theorem eqRepData_idxOk {ψ : Name → Nat} {ρp : Nat → V}
    (hA : ρp 1 ∈ˢ (univ (ψ uN) : V)) : IdxOk (ψ uN) ρp eqIds := by
  have hi : interp V ρp (AnnotTerm.bvar 1) = ρp 1 := interp_bvar V ρp 1
  exact ⟨⟨trivial, fun _ => by rw [hi]; exact hA, fun _ _ => trivial⟩,
    ⟨by rw [hi]; exact hA, fun _ _ => trivial⟩⟩

/-! ## The chains

One constructor, no fields: its X-chain is the single index equation
`a = ⟨t⟩₀`, and the recursive slots' fit is vacuous. -/

/-- **The X-chains are graded at every family and tuple** — the one
chain is the index equation, whose two sides read off the frame. -/
theorem eqRepData_chainsOk {ψ : Name → Nat} {ρp : Nat → V}
    (hI : IdxOk (ψ uN) ρp eqIds) :
    XChainsOk (ψ uN) 0 ρp eqIds [[]] [[]] [[]] [[]] [eqEs] := by
  have hok : FixChainsOkI (ψ uN) 0 ρp eqIds eqIds.length [[]] [[]] [[]] [[]] [eqEs] := by
    intro X _ t ht Fs hFs
    rcases List.mem_cons.mp hFs with rfl | h
    · refine FieldsOkB_append_idxEq (Fs := []) trivial fun bs hsp => ?_
      obtain rfl : bs = [] := List.length_eq_zero_iff.mp hsp.length_eq
      refine eqsXI_wellDenoted (Ids := eqIds) hI ht rfl (fun E hE' => ?_) rfl
      rcases List.mem_cons.mp hE' with rfl | hE'
      · exact trivial
      · exact nomatch hE'
    · exact nomatch h
  refine ⟨hI, hok, fun _ _ _ _ j hj => ?_, fixFunVI_closed_zero hok⟩
  obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
  exact trivial

/-! ## The functor's fibre

The chain has no fields, so the fibre at `(X, t)` is `{pt}` when the
index equation holds there and `∅` otherwise — independently of `X`,
which is what makes the least fixed point the functor's own value. -/

/-- **The fibre's membership**, spelled at the block's data. -/
theorem eqRepData_step_iff {ψ : Name → Nat} {ρp : Nat → V} {X t x : V} :
    x ∈ˢ fixStepI (ψ uN) 0 ρp eqIds 1 [[]] [[]] [[]] [[]] [eqEs] X t ↔
      x = pt ∧ EqAll (cons t (cons X ρp)) (eqsXI 1 0 eqEs) := by
  constructor
  · intro hx
    obtain ⟨rfl, j, fs, hj, hlen, -, hall⟩ := fixStepI_zero_elim (Ids := eqIds) hx
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    obtain rfl : fs = [] := List.length_eq_zero_iff.mp hlen
    exact ⟨rfl, hall⟩
  · rintro ⟨rfl, hall⟩
    show (pt : V) ∈ˢ sumSet 0 (sumFibre 0 (cons t (cons X ρp))
      (chainsXI (ψ uN) eqIds 1 [[]] [[]] [[]] [[]] [eqEs]))
    refine pt_mem_sumSet_zero (i := 0) (a := pt) ?_
    rw [sumFibre_of_getElem? (Fs := [idxEqAV (eqsXI 1 0 eqEs)]) rfl]
    exact pt_mem_tower_teleOfFields
      (spineFit_append_idxEq (Fs := []).mpr ⟨[], rfl, trivial, hall⟩)

/-- The index equation at a tuple: it holds exactly when the
constructor's index expression — the parameter `a` — is the tuple's
sole component. -/
theorem eqRepData_eqAll_iff {ψ : Name → Nat} {ρp : Nat → V}
    (hI : IdxOk (ψ uN) ρp eqIds) {X b : V} (hb : b ∈ˢ ρp 1) :
    EqAll (cons (tupW (ψ uN) [b]) (cons X ρp)) (eqsXI 1 0 eqEs) ↔ ρp 0 = b := by
  have hsp : SpineFit ρp eqIds [b] := ⟨by rw [interp_bvar]; exact hb, trivial⟩
  have h := EqAll_eqsXI (V := V) (u := ψ uN) (ρp := ρp) (Ids := eqIds) hI (X := X) (is := [b]) hsp
    (bs := []) (nF := 0) rfl (Es := eqEs)
  rw [show consList ([] : List V) (cons (tupW (ψ uN) [b]) (cons X ρp))
    = cons (tupW (ψ uN) [b]) (cons X ρp) from rfl,
    show eqIds.length = 1 from rfl] at h
  rw [h]
  constructor
  · intro hh
    have := hh 0 Nat.zero_lt_one
    rwa [show (eqEs.getD 0 default : AnnotTerm) = .bvar 0 from rfl, interp_bvar] at this
  · intro hh l hl
    obtain rfl : l = 0 := Nat.lt_one_iff.mp hl
    rw [show (eqEs.getD 0 default : AnnotTerm) = .bvar 0 from rfl, interp_bvar]
    exact hh

/-- **The least fixed point is the truth value of the index
equation** — the `Eq` leaf. -/
theorem eqRepData_lfp {ψ : Name → Nat} {ρp : Nat → V}
    (hA : ρp 1 ∈ˢ (univ (ψ uN) : V)) {b : V} (hb : b ∈ˢ ρp 1) :
    app (lfpFamSet 0 (idxSet (ψ uN) ρp eqIds)
      (fixFunVI (ψ uN) 0 ρp eqIds 1 [[]] [[]] [[]] [[]] [eqEs])) (tupW (ψ uN) [b])
      = eqv (ρp 0) b := by
  have hI : IdxOk (ψ uN) ρp eqIds := eqRepData_idxOk hA
  have hX := eqRepData_chainsOk (V := V) hI
  have hsp : SpineFit ρp eqIds [b] := ⟨by rw [interp_bvar]; exact hb, trivial⟩
  have ht : tupW (ψ uN) [b] ∈ˢ idxSet (ψ uN) ρp eqIds := tupW_mem hsp
  have hfix := fixFamI_app_eq (V := V) (Ids := eqIds) hX ht
  have hgoal : app (lfpFamSet 0 (idxSet (ψ uN) ρp eqIds)
        (fixFunVI (ψ uN) 0 ρp eqIds 1 [[]] [[]] [[]] [[]] [eqEs])) (tupW (ψ uN) [b])
      = fixStepI (ψ uN) 0 ρp eqIds 1 [[]] [[]] [[]] [[]] [eqEs]
          (fixFamI (ψ uN) 0 ρp eqIds 1 [[]] [[]] [[]] [[]] [eqEs]) (tupW (ψ uN) [b]) := hfix.symm
  rw [hgoal]
  refine Eq.symm (Subset.antisymm (fun x hx => ?_) (fun x hx => ?_))
  · have hxpt : x = pt := eq_pt_of_mem_univZero (eqv_mem_univZero _ _) hx
    have hab : ρp 0 = b := eq_of_mem_eqv hx
    subst hxpt
    exact eqRepData_step_iff.mpr ⟨rfl, (eqRepData_eqAll_iff hI hb).mpr hab⟩
  · obtain ⟨rfl, hall⟩ := eqRepData_step_iff.mp hx
    rw [(eqRepData_eqAll_iff hI hb).mp hall]
    exact pt_mem_eqv_self b

end

/-! ## The two type readings -/

/-- **`Eq`'s type reading** at any environment: the block's type
mentions no constant, so the reading is the Π-tower of the datum's
parameter-and-index data over `Prop`. -/
theorem denoteMeta_eqA_typeR {acval : Name → (Name → Nat) → AnnotTerm} {env' : Env}
    (ψ : Name → Nat) :
    denoteMeta acval env' ψ 0 eqA.toConstantVal.type
      = some (.pi 0 1 (.sort (ψ uN)) (.pi 0 1 (.bvar 0) (.pi 0 1 (.bvar 1) (.sort 0)))) := by
  simp [eqA, ConstantInfo.toConstantVal, denoteMeta_forallE, denoteMeta_sort,
    denoteMeta_fvar, Expr.instantiate1, pwBit_never, Level.eval, uN]

/-- **`Eq.refl`'s type reading** at the `Eq.rec` extension: two
squash-regime parameter binders over the `Eq` spine at the tower. -/
theorem denoteMeta_eqReflA_typeR {m : EnvModel V env} {A : (Name → Nat) → AnnotTerm}
    (ψ : Name → Nat) (hE : env.find? eqName = some eqA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValAV ψ) :
    denoteMeta (acvalWith m.acval eqRecA.name A) ⟨eqRecA :: env.consts⟩ ψ 0
        eqReflA.toConstantVal.type
      = some (.pi 0 0 (.sort (ψ uN)) (.pi 0 0 (.bvar 0)
          (.app (.app (.app (eqValAV ψ) (.bvar 1)) (.bvar 0)) (.bvar 0)))) := by
  have hEc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval eqRecA.name A) ⟨eqRecA :: env.consts⟩ ψ d
        (.const eqName [.param uN]) = some (eqValAV ψ) := by
    intro d
    rw [denoteMeta_eqLeaf (m := m) (A := A) ψ (Level.param uN) (by decide) hE d,
      show ([Level.param uN] : List Level) = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN], hEv]
  rw [show eqReflA.toConstantVal.type
      = Expr.forallE (.sort (.param uN))
          (Expr.forallE (.bvar 0)
            (.app (.app (.app (.const eqName [.param uN]) (.bvar 1))
              (.bvar 0)) (.bvar 0))
            { pw := .ifAllZero [] })
          { pw := .ifAllZero [] } from rfl]
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
    Expr.instantiate1, pwBit_ifAllZero_nil, hEc, Level.eval]

/-- **`Eq.refl`'s type reading is graded** — two `Prop`-valued binders
over the `Eq` spine, whose grading is the tower's own. -/
theorem eqReflTyR_wellDenotedV (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (.pi 0 0 (.sort (ψ uN)) (.pi 0 0 (.bvar 0)
      (.app (.app (.app (eqValAV ψ) (.bvar 1)) (.bvar 0)) (.bvar 0)))) := by
  have hstep : ∀ Aset x : V, Aset ∈ˢ (univ (ψ uN) : V) → x ∈ˢ Aset →
      WellDenotedV V (cons x (cons Aset ρ))
          (.app (.app (.app (eqValAV ψ) (.bvar 1)) (.bvar 0)) (.bvar 0)) ∧
        interp V (cons x (cons Aset ρ))
          (.app (.app (.app (eqValAV ψ) (.bvar 1)) (.bvar 0)) (.bvar 0)) ∈ˢ (univZero : V) := by
    intro Aset x hA hx
    have hAi : interp V (cons x (cons Aset ρ)) (AnnotTerm.bvar 1) = Aset := by
      rw [interp_bvar]; rfl
    have hxi : interp V (cons x (cons Aset ρ)) (AnnotTerm.bvar 0) = x := by
      rw [interp_bvar]; rfl
    exact eqValAV_app₃_okP ψ _ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩
      (by rw [hAi]; exact hA) (by rw [hAi, hxi]; exact hx) (by rw [hAi, hxi]; exact hx)
  refine (WellDenotedV_pi_zero (Aa := .sort (ψ uN)) ⟨trivial, trivial⟩ ?_ ?_).1
  all_goals (
    intro Aset hAset
    rw [interp_sort] at hAset
    have hlev := WellDenotedV_pi_zero (Aa := AnnotTerm.bvar 0) (ρ := cons Aset ρ)
      ⟨trivial, trivial⟩
      (fun x hx => (hstep Aset x hAset (by rwa [interp_bvar] at hx)).1)
      (fun x hx => (hstep Aset x hAset (by rwa [interp_bvar] at hx)).2))
  case _ => exact hlev.1
  case _ => exact hlev.2

/-! ## The representation -/

/-- **The pinned `Eq` block is represented** — the obligation
`declStep_preserves_of_basis_rec_cons` owes at the `Eq.rec` cons. -/
theorem indRepsHead_eqRec (mp : EnvModelM V μ env)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, mp.base2.acval eqName ψ = eqValAV ψ)
    (hRv : ∀ ψ : Name → Nat, mp.base2.acval eqReflName ψ = eqReflValAV ψ)
    (hfresh : env.find? eqRecA.name = none) :
    ∀ m₂ : EnvModel V ⟨eqRecA :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval eqRecA.name eqRecValAV →
      IndRepsHead env eqRecA m₂ := by
  intro m₂ hac cvR mI rP rules hc T hT
  injection hc with h1 h2 h3 h4
  subst h1 h2 h3 h4
  have hT' : T = eqName := by
    have h := hT
    simp only at h
    exact (Name.str.inj h).1.symm
  subst hT'
  have hEleaf : ∀ ψ : Name → Nat, m₂.acval eqName ψ = eqValAV ψ := by
    intro ψ; rw [hac, acvalWith_ne (by decide)]; exact hEv ψ
  have hRleaf : ∀ ψ : Name → Nat, m₂.acval eqReflName ψ = eqReflValAV ψ := by
    intro ψ; rw [hac, acvalWith_ne (by decide)]; exact hRv ψ
  have hread : ∀ ψ : Name → Nat,
      denoteMeta m₂.acval ⟨eqRecA :: env.consts⟩ ψ 0 eqReflA.toConstantVal.type
        = some (.pi 0 0 (.sort (ψ uN)) (.pi 0 0 (.bvar 0)
            (.app (.app (.app (eqValAV ψ) (.bvar 1)) (.bvar 0)) (.bvar 0)))) := by
    intro ψ
    rw [hac]
    exact denoteMeta_eqReflA_typeR (m := mp.base2) (A := eqRecValAV) ψ hE hEv
  -- the recursor's type reading (task #279 M-A′), used by `recRead` and
  -- by the member's `RecReadAt`
  have hrecRead : ∀ ψ : Name → Nat,
      denoteMeta m₂.acval ⟨eqRecA :: env.consts⟩ ψ 0 eqRecA.toConstantVal.type
        = some (mkPisAV ((eqRepData (V := V) ⟨eqRecA :: env.consts⟩).recDataAV m₂ ψ 0)
            (mutualConcAV (eqRepData (V := V) ⟨eqRecA :: env.consts⟩).k
              (eqRepData (V := V) ⟨eqRecA :: env.consts⟩).nAll
              ((eqRepData (V := V) ⟨eqRecA :: env.consts⟩).nIdxAt 0) 0)) := by
    intro ψ
    rw [hac]
    refine (denoteMeta_eqRecA_type (m := mp.base2) ψ hE hR hEv hRv).trans ?_
    congr 1
    show eqRecTy (pwBit ψ (.ifAllZero [u1N])) ψ
      = mkPisAV (recDataAVP m₂ ψ [m₂.acval eqName ψ] (fun _ => paramBvarsAt 2 2) 2 [1]
          (.param u1N) [(0, 1, .sort (ψ uN)), (0, 1, .bvar 0)] [[(0, 1, .bvar 1)]]
          [(eqReflName, 0, [(0, 0, .sort (ψ uN)), (0, 0, .bvar 0)], eqEs, [], [], [])]
          (fun _ => 0) (fun _ _ => 0) 0)
        (mutualConcAV 1 1 1 0)
    rw [recDataAVP_params, mutualRecDataAV_one, hEleaf ψ, mutualConcAV_one]
    unfold fixRecDataAVL fixMinorsData fixMinorsDataM minorAVAtRM
    rw [hRleaf ψ]
    simp only [List.length_nil, AnnotTerm.liftN_zero]
    rfl
  refine Or.inl ⟨_, _, eqRepData ⟨eqRecA :: env.consts⟩, 0,
    ConLeche.Env.find?_cons_of_fresh hfresh hE, ?_⟩
  refine {
    member := rfl
    strip := ⟨_, rfl⟩
    isProp := rfl
    rulesRead := ?_
    mI := rfl
    rP := rfl
    rules := fun _ => rfl
    kRealLe := Nat.le_refl _
    memReal := Nat.zero_lt_one
    recName := rfl
    recNamesReal := fun _ _ => rfl
    tgtsRLt := fun _ _ => Nat.zero_lt_one
    membersFound := fun t ht => by
      obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
      exact ⟨_, _, ConLeche.Env.find?_cons_of_fresh hfresh hE⟩
    membersLps := membersLps_one rfl (ConLeche.Env.find?_cons_of_fresh hfresh hE)
    memberNodup := memberNodup_one rfl
    memsReal := fun j hj => ⟨fun _ => hj, fun _ => Nat.zero_lt_one⟩
    ctorsCFound := fun _ h => nomatch h
    pinsReal := fun _ _ => ⟨fun _ => rfl, rfl⟩
    recRead := ?_
    former := ?fd
    formersRead := IndRep.formersRead_one rfl rfl
      (ConLeche.Env.find?_cons_of_fresh hfresh hE) ?fd
    leafShape := fun t ht ψ => by
      obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
      exact ⟨.eqE (.bvar 1) (.bvar 0), hEleaf ψ⟩
    ctors := ?_
    memsFound := fun _ _ => ⟨⟨_, _, ConLeche.Env.find?_cons_of_fresh hfresh hE⟩,
      fun _ => ⟨_, _, ConLeche.Env.find?_cons_of_fresh hfresh hE⟩⟩
    idxRes := ?_
    uParams := fun _ _ h => h uN List.mem_cons_self
    paramsIff := fun _ _ _ _ _ => Iff.rfl
    paramsIffM := fun t ht _ _ => by
      obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
      exact Iff.rfl
    chains := ?_
    functor := ?_
    fibre := ?_
    leaf := ?_
    tupMem := fun ψ ρp _ is hi => by
      show tupW (ψ uN) is ∈ˢ idxSet (ψ uN) ρp eqIds
      exact tupW_mem hi
    ctor := ?_
    mkZero := fun _ _ _ _ => rfl
    mkInj := fun _ hz => absurd rfl hz
    -- task #279 M-C′: the one constructor has no fields, its reading is
    -- the parameter `a`, and the tuple is `⟨a⟩`
    idxRecover := fun ψ ρp hρ is hsp X j fs hj hlen _ _ hall => by
      obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
      have hlen0 : fs.length = 0 := hlen
      obtain rfl : fs = [] := List.length_eq_zero_iff.mp hlen0
      have hislen : is.length = 1 := hsp.length_eq
      obtain ⟨b, rfl⟩ : ∃ b, is = [b] := by
        match is, hislen with
        | [b], _ => exact ⟨b, rfl⟩
      have hb : b ∈ˢ ρp 1 := hsp.1
      have hI := eqRepData_idxOk (eqRepData_frame hρ).1
      have hall' : EqAll (cons (tupW (ψ uN) [b]) (cons X ρp)) (eqsXI 1 0 eqEs) := hall
      have h := (eqRepData_eqAll_iff hI hb).mp hall'
      exact ⟨rfl, by show [ρp 0] = [b]; rw [h]⟩
    slotRecover := fun _ _ _ j i hj hri _ _ _ _ => by
      obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
      have hri' : ([] : List Bool).getD i false = true := hri
      simp at hri' }
  · -- the recursor's readings (task #279 M-A′/M-B′): `Eq.rec`, the one
    -- member, with its one rule
    intro _ _ t ht
    obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
    refine ⟨eqRecA.toConstantVal, 5, 4, [eqRecRule], ?_, rfl, rfl, rfl, hrecRead, rfl,
      fun j cA hj hmm => ?_, ?_⟩
    · show Env.find? ⟨eqRecA :: env.consts⟩ eqRecA.name
        = some (.recInfo eqRecA.toConstantVal 5 4 [eqRecRule])
      rw [ConLeche.Env.find?_cons, if_pos rfl]
      rfl
    · match j, hj with
      | 0, hj =>
        obtain rfl : cA = (eqReflA.toConstantVal, 0) := (Option.some.inj hj).symm
        refine ⟨eqRecRule, List.mem_cons_self, rfl, fun _ => ⟨rfl, rfl, rfl⟩, fun ψ => ?_⟩
        rw [hac]
        refine (denoteMeta_eqRec_rhs (m := mp.base2) ψ hE hR hEv hRv).trans ?_
        congr 1
        show eqRecRa (pwBit ψ (.ifAllZero [u1N])) ψ
          = mkLamsAV (ruleDataAVP m₂ ψ [m₂.acval eqName ψ] (fun _ => paramBvarsAt 2 2) 2 [1]
              (.param u1N) [(0, 1, .sort (ψ uN)), (0, 1, .bvar 0)] [[(0, 1, .bvar 1)]]
              [(eqReflName, 0, [(0, 0, .sort (ψ uN)), (0, 0, .bvar 0)], eqEs, [], [], [])]
              (fun _ => 0) (fun _ _ => 0) [(0, 0, .sort (ψ uN)), (0, 0, .bvar 0)])
            (mutualRuleCoreAV (pwBit ψ (Level.zeronessOf (.param u1N)))
              (fun t => m₂.acval (([eqName].getD t .anonymous).str "rec") ψ) (fun _ => 0) 2 1 1 0 0
              [] [] [])
        rw [ruleDataAVP_params, mutualRuleDataAV_one]
        unfold fixRuleDataAV motiveAVI fixMinorsData fixMinorsDataM minorAVAtRM mutualRuleCoreAV
        rw [hEleaf ψ, hRleaf ψ]
        simp only [List.length_nil, AnnotTerm.liftN_zero]
        rfl
    · -- the motive walk (task #279 M-B′ step 3a): `Eq.rec`'s one motive
      -- is recognised wherever `Eq` is stored, and its minor stops the
      -- walk syntactically
      refine ⟨_, _, rfl, fun env' hst => ?_⟩
      obtain ⟨cv, caps, hf⟩ := hst 0 Nat.zero_lt_one
      have hf' : env'.find? eqName = some (.indInfo cv caps) := hf
      show (match (if (match env'.find? eqName with
            | some (.indInfo _ _) => true
            | _ => false) = true then some eqName else none) with
        | some C => C :: containerMembersGo env' 2 4 1 _
        | none => []) = [eqName]
      rw [hf']
      rfl
  · -- the recursor's type reading (task #279 M-A′)
    intro ψ
    exact hrecRead ψ
  · -- the former's data
    refine ⟨fun ψ => denoteMeta_eqA_typeR ψ, (fun _ => rfl), ?_, fun ψ ρ => ?_,
      (fun _ => ⟨trivial, (by apply bvarsBelow_bvarAV; omega),
        (by apply bvarsBelow_bvarAV; omega), trivial⟩),
      (fun ψ₁ ψ₂ h => ⟨by rw [eqRepData_pps, eqRepData_pps, h uN List.mem_cons_self], rfl⟩),
      (fun _ => rfl), ?_, fun ψ₁ ψ₂ h => by
        show [ψ₁ uN + 1, ψ₁ uN, ψ₁ uN] = [ψ₂ uN + 1, ψ₂ uN, ψ₂ uN]
        rw [h uN List.mem_cons_self]⟩
    · intro ψ d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact Nat.one_ne_zero
      rcases List.mem_cons.mp hd with rfl | hd
      · exact Nat.one_ne_zero
      rcases List.mem_cons.mp hd with rfl | hd
      · exact Nat.one_ne_zero
      · exact nomatch hd
    · show WellDenotedV V ρ (.pi 0 1 (.sort (ψ uN)) (.pi 0 1 (.bvar 0)
        (.pi 0 1 (.bvar 1) (.sort 0))))
      exact ⟨⟨trivial, fun _ _ => ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩⟩,
        ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial,
            fun h => absurd h Nat.one_ne_zero⟩,
          fun h => absurd h Nat.one_ne_zero⟩,
        fun h => absurd h Nat.one_ne_zero⟩⟩
    · -- the parameter binders' universes
      intro ψ i hi ρ hs
      match i, hi with
      | 0, _ =>
        show (univ (ψ uN) : V) ∈ˢ univ (ψ uN + 1)
        exact univ_mem_univ _
      | 1, _ =>
        show ρ 0 ∈ˢ (univ (ψ uN) : V)
        exact hs 0 _ rfl
      | 2, _ =>
        show ρ 1 ∈ˢ (univ (ψ uN) : V)
        exact hs 1 _ rfl
  · -- the constructor's data
    intro j cA hj
    match j, hj with
    | 0, hj =>
      obtain rfl : cA = (eqReflA.toConstantVal, 0) := (Option.some.inj hj).symm
      refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hR, rfl, ?_⟩
      refine {
        resid := ⟨_, [.bvar 0], rfl, rfl⟩
        read := fun ψ => ?_
        len := fun _ => rfl
        lenE := fun _ => rfl
        idxLen := rfl
        idxRead := fun _ => .cons (denoteMeta_fvar _ _ _ _) .nil
        bits := fun _ d hd => ?_
        okTy := fun ψ ρ => ?_
        below := fun _ => ⟨trivial, (by apply bvarsBelow_bvarAV; omega), trivial⟩
        belowE := fun _ E hE' => ?_
        params := fun ψ₁ ψ₂ h =>
          ⟨by rw [eqRepData_dsF, eqRepData_dsF, h uN List.mem_cons_self], rfl⟩
        srcLen := rfl
        srcBnd := fun _ h => nomatch h
        srcIdx := fun _ _ h => nomatch h
        srcProp := fun _ _ _ _ _ => trivial
        opened := ⟨?_, (fun _ _ h => nomatch h), (fun _ _ h => nomatch h),
          (fun _ _ h => nomatch h), fun _ h => absurd h (Nat.not_lt_zero _)⟩
        opens := ⟨_, rfl, rfl⟩
        ksLen := rfl
        xLen := rfl
        pLen := rfl
        xIdx := fun _ _ h => nomatch h
        pIdx := fun k x hk => ?_
        idxEq := rfl
        domRead := fun _ _ _ h => nomatch h
        eissLen := fun _ => rfl
        eisRead := fun _ _ _ h => nomatch h
        eisLen := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
        recEntry := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
        eissParams := fun _ _ _ => rfl
        eissBelow := fun _ _ _ h => nomatch h
        ordNone := fun _ _ _ _ => rfl
        tssLen := fun _ => rfl
        tssNone := fun _ _ _ => rfl
        tssBits := fun _ _ _ h => nomatch h
        tssPiBits := fun _ _ _ h => nomatch h
        tssBelow := fun _ _ => trivial
        tssParams := fun _ _ _ => rfl
        reflOpen := fun _ _ _ h => nomatch h
        eisLenRefl := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
        reflEntry := fun _ _ _ h => absurd h (Nat.not_lt_zero _) }
      · -- the reading
        rw [hread ψ]
        show some _ = some (mkPisAV [(0, 0, .sort (ψ uN)), (0, 0, .bvar 0)]
          (AnnotTerm.mkAppN (m₂.acval eqName ψ) (paramBvars 2 0 ++ eqEs)))
        rw [hEleaf ψ]
        rfl
      · rcases List.mem_cons.mp hd with rfl | hd
        · exact ⟨fun _ => rfl, fun _ => rfl⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact ⟨fun _ => rfl, fun _ => rfl⟩
        · exact nomatch hd
      · -- the reading is graded
        show WellDenotedV V ρ (mkPisAV [(0, 0, .sort (ψ uN)), (0, 0, .bvar 0)]
          (AnnotTerm.mkAppN (m₂.acval eqName ψ) (paramBvars 2 0 ++ eqEs)))
        rw [hEleaf ψ]
        exact eqReflTyR_wellDenotedV ψ ρ
      · rcases List.mem_cons.mp hE' with rfl | hE'
        · show (0 : Nat) < 2 + 0
          omega
        · exact nomatch hE'
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · rfl
        · exact nomatch he
      · match k, hk with
        | 0, hk => exact ⟨_, (Option.some.inj hk).symm⟩
        | 1, hk => exact ⟨_, (Option.some.inj hk).symm⟩
  · -- the residual's index arguments resolve
    intro j cA hj e he
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · exact nomatch he
  · -- the chains
    intro ψ ρp hρ
    exact xChainsOk_toChainsOk (eqRepData_chainsOk (eqRepData_idxOk (eqRepData_frame hρ).1))
  · -- the functor
    intro ψ ρp hρ
    have hX := eqRepData_chainsOk (V := V) (eqRepData_idxOk (eqRepData_frame hρ).1)
    exact ⟨fixFunVI_mem hX.hok, fixFunVI_mono hX, fixFunVI_maps hX, fixFunVI_closed_exists hX⟩
  · -- the fibre
    intro ψ ρp hρ X hX t ht x
    have hI := eqRepData_idxOk (V := V) (eqRepData_frame hρ).1
    have hXs : X ∈ˢ lfpFamSpace V 0 (idxSet (ψ uN) ρp eqIds) := by
      rw [lfpFamSpace_eq]; exact hX
    have ht' : t ∈ˢ idxSet (ψ uN) ρp eqIds := ht
    show x ∈ˢ app (app (fixFunVI (ψ uN) 0 ρp eqIds 1 [[]] [[]] [[]] [[]] [eqEs]) X) t ↔ _
    rw [fixFunVI_app hXs, famFI_app ht', eqRepData_step_iff]
    constructor
    · rintro ⟨rfl, hall⟩
      exact ⟨0, [], Nat.zero_lt_one, ⟨rfl, trivial, hall⟩, rfl⟩
    · rintro ⟨j, fs, hj, ⟨hlen, -, hall⟩, rfl⟩
      obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
      obtain rfl : fs = [] := List.length_eq_zero_iff.mp hlen
      exact ⟨rfl, hall⟩
  · -- the leaf
    intro ψ ρ as is hsp₁ hsp₂
    match as, hsp₁ with
    | [A, a], hsp₁ =>
      match is, hsp₂ with
      | [b], hsp₂ =>
        have hA : A ∈ˢ (univ (ψ uN) : V) := by
          have := hsp₁.1; rwa [interp_sort] at this
        have ha : a ∈ˢ A := by
          have := hsp₁.2.1; rwa [interp_bvar] at this
        have hb : b ∈ˢ A := by
          have := hsp₂.1; rwa [interp_bvar] at this
        show ([A, a] ++ [b]).foldl app (interp V ρ (m₂.acval eqName ψ)) = _
        rw [hEleaf ψ]
        show app (app (app (interp V ρ (eqValAV ψ)) A) a) b = _
        rw [eqValAV_app₃ ψ ρ A a b hA ha hb]
        exact (eqRepData_lfp (ρp := consList [A, a] ρ) hA hb).symm
  · -- the constructor's value
    intro j cA hj ψ ρ as fs hsp₁ hsp₂
    match j, hj with
    | 0, hj =>
      obtain rfl : cA = (eqReflA.toConstantVal, 0) := (Option.some.inj hj).symm
      obtain rfl : fs = [] := List.length_eq_zero_iff.mp hsp₂.length_eq
      show (as ++ []).foldl app (interp V ρ (m₂.acval eqReflName ψ)) = pt
      rw [hRleaf ψ, eqReflValAV_interp]
      exact foldl_app_pt' _

end EqRep

/-- **`Eq.rec`, installed at the P tier.** -/
theorem extendEqRec (mp : EnvModelM V μ env)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, mp.base2.acval eqName ψ = eqValAV ψ)
    (hRv : ∀ ψ : Name → Nat,
      mp.base2.acval eqReflName ψ = eqReflValAV ψ)
    (hfresh : env.find? eqRecA.name = none)
    (hwf : EnvWF ⟨eqRecA :: env.consts⟩) :
    ∃ mp' : EnvModelM V μ ⟨eqRecA :: env.consts⟩,
      mp'.base2.acval
        = acvalWith mp.base2.acval eqRecA.name eqRecValAV := by
  have hty := fun ψ =>
    denoteMeta_eqRecA_type (m := mp.base2) (A := eqRecValAV) ψ hE hR hEv hRv
  have hz : ∀ ψ : Name → Nat,
      pwBit ψ (ConLeche.PropWhen.ifAllZero [u1N]) = 0 ↔ ψ u1N = 0 :=
    fun ψ => pwBit_ifAllZero_single ψ u1N
  refine declStep_preserves_of_basis_rec_cons mp
    (hreps := indRepsHead_eqRec mp hE hR hEv hRv hfresh)
    (A := eqRecValAV) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf
      (fun ψ => by rw [eqRecValAV_erase ψ]; exact eqRecValT_closed ψ)
      rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT eqRecA.name ψ
          = none from rfl] at hp
        exact nomatch hp)
      (fun _ h => nomatch h)
      (fun _ _ _ _ heq r hr => by
        injection heq with _ _ _ h4
        rw [← h4] at hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨⟨_, _, _, hR⟩, fun _ => recRuleKOf_of hR rfl hE rfl,
            fun hb => Bool.noConfusion hb⟩
        · exact nomatch hr'))
    (fun ψ k => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le k)
        (by rw [eqRecValAV_erase]; exact eqRecValT_closed ψ)) 1)
    (fun ψ₁ ψ₂ hp => eqRecValAV_congr
      (hp uN (by
        show uN ∈ [u1N, uN]
        exact List.mem_cons_of_mem _ List.mem_cons_self))
      (hp u1N (by show u1N ∈ [u1N, uN]; exact List.mem_cons_self)))
    (fun ψ ρ => ((bitAgree_wellDenotedV (bitAgree_eqRecValAV ψ) ρ).mp
      (eqRecRaTower_data ψ (hz ψ) ρ).1).1)
    (fun ψ ρ => ((bitAgree_wellDenotedV (bitAgree_eqRecValAV ψ) ρ).mp
      (eqRecRaTower_data ψ (hz ψ) ρ).1).2)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact eqRecTy_wellDenotedV ψ (hz ψ) ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [← AnnotTerm.BitAgree.interp_eq V (bitAgree_eqRecValAV ψ) ρ]
    exact (eqRecRaTower_data ψ (hz ψ) ρ).2
  · intro m₂ hac φ
    refine recRules_cons_rec mp hfresh eqRecA_eq m₂ hac φ ?_
    intro rl hrl _
    rcases List.mem_cons.mp hrl with rfl | hr'
    · exact eqRecLaw (m := mp.base2) m₂ hE hR hEv hRv hac φ
    · exact nomatch hr'

/-- **The `Eq` block, installed at the P tier.**  `BasisStepPB`'s
`eqK` branch — the block whose chain reads its own earlier leaves, and
so the one that consumes the install's exposed `acval`. -/
theorem declBasisPB_eqK {env₁ : Env} (mp : EnvModelM V μ env)
    (h : ConLeche.Semantics.BasisInstallRun env
      ConLeche.BasisKind.eqK.declsA env₁) :
    Nonempty (EnvModelM V μ env₁) := by
  rw [show ConLeche.BasisKind.eqK.declsA = [eqA, eqReflA, eqRecA]
    from rfl] at h
  obtain ⟨h1, h2, h3, hnil⟩ := h
  subst hnil
  have hf1 : env.find? eqName = none := Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨eqA :: env.consts⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
  obtain ⟨mp1, hac1⟩ := extendEq mp hf1 hwf1
  have hEv1 : ∀ ψ : Name → Nat, mp1.base2.acval eqName ψ
      = eqValAV ψ := by
    intro ψ
    rw [hac1, show eqName = eqA.name from rfl, acvalWith_self]
  have hE1 : (⟨eqA :: env.consts⟩ : Env).find? eqName = some eqA := by
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl
  have hf2 : (⟨eqA :: env.consts⟩ : Env).find? eqReflA.name = none :=
    Option.isNone_iff_eq_none.mp h2
  have hwf2 : EnvWF ⟨eqReflA :: eqA :: env.consts⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ eqReflA.toConstantVal.type = true
    have hf : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqName
        = some eqA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hE1
    rw [show eqReflA.toConstantVal.type
        = Expr.forallE (.sort (.param uN))
            (Expr.forallE (.bvar 0)
              (.app (.app (.app (.const eqName [.param uN]) (.bvar 1))
                (.bvar 0)) (.bvar 0))
              { pw := .ifAllZero [] })
            { pw := .ifAllZero [] } from rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨mp2, hac2⟩ := extendEqRefl mp1 hE1 hEv1 hf2 hwf2
  have hE2 : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqName
      = some eqA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hE1
  have hR2 : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqReflName
      = some eqReflA := by
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl
  have hEv2 : ∀ ψ : Name → Nat, mp2.base2.acval eqName ψ
      = eqValAV ψ := by
    intro ψ
    rw [hac2, acvalWith_ne (by decide)]
    exact hEv1 ψ
  have hRv2 : ∀ ψ : Name → Nat, mp2.base2.acval eqReflName ψ
      = eqReflValAV ψ := by
    intro ψ
    rw [hac2, show eqReflName = eqReflA.name from rfl, acvalWith_self]
  have hf3 : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find?
      eqRecA.name = none := Option.isNone_iff_eq_none.mp h3
  have hwf3 : EnvWF ⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ := by
    have hfE : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find?
        eqName = some eqA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hE2
    have hfR : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find?
        eqReflName = some eqReflA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hR2
    refine EnvWF.cons hwf2 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), ?_,
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    · show Expr.constsResolve _ eqRecA.toConstantVal.type = true
      rw [show eqRecA.toConstantVal.type
          = Expr.forallE (.sort (.param uN))
              (Expr.forallE (.bvar 0)
                (Expr.forallE
                  (Expr.forallE (.bvar 1)
                    (Expr.forallE
                      (.app (.app (.app (.const eqName [.param uN])
                        (.bvar 2)) (.bvar 1)) (.bvar 0))
                      (.sort (.param u1N))
                      { pw := .never })
                    { pw := .never })
                  (Expr.forallE
                    (.app (.app (.bvar 0) (.bvar 1))
                      (.app (.app (.const eqReflName [.param uN])
                        (.bvar 2)) (.bvar 1)))
                    (Expr.forallE (.bvar 3)
                      (Expr.forallE
                        (.app (.app (.app (.const eqName [.param uN])
                          (.bvar 4)) (.bvar 3)) (.bvar 0))
                        (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
                        { pw := .ifAllZero [u1N] })
                      { pw := .ifAllZero [u1N] })
                    { pw := .ifAllZero [u1N] })
                  { pw := .ifAllZero [u1N] })
                { pw := .ifAllZero [u1N] })
              { pw := .ifAllZero [u1N] } from rfl]
      simp [Expr.constsResolve, hfE, hfR]
    · intro cv mI rP rules heq
      injection heq with h1' _ _ h4'
      subst h1'; subst h4'
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact ⟨rfl, rfl, by
          show Expr.constsResolve _ (RecRule.rhs eqRecRule) = true
          simp [Expr.constsResolve, eqRecRule, hfE, hfR], rfl,
          fun lvls pins heqf => nomatch heqf⟩
      · exact nomatch hr'
  obtain ⟨mp3, -⟩ := extendEqRec mp2 hE2 hR2 hEv2 hRv2 hf3 hwf3
  exact ⟨mp3⟩

end Eq

end ConLeche.Model
