module

public import ConLeche.Model.BasisQuot
import ConLeche.Semantics.BasisRules
import ConLeche.Model.BasisLfp
import ConLeche.Model.Cover

public section

/-!
# The `Eq` block, P tier (task #161, ENDGAME H)

The one block the layer does not carry: there is no `BConst` for `Eq`,
so nothing here goes through `BConst.typeAV`/`bval_mem_type`
— every type reading's grading and membership is discharged against
the block's **own** towers (`Model/EqTower.lean`).

Two structural consequences:

* the `Eq` cons is the tier's one `eq_law`-bespoke cons
  (`eqLaw_cons_fresh`'s side condition is `eqName ≠ c₀.name`), and it
  is discharged by `eqLaw_of_tower` through
  `declStep_preserves_of_basis_cons_eqrow`;
* `Eq.rec`'s stored rule returns its **minor premise**, so its fired
  equality is an identity between two collapsed towers rather than a
  value law — and the only real content is that the major premise's
  membership forces `a = b` and the proof to be `pt`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (eqValT eqReflValT eqRecValT)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule uN u1N vN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

section Eq

open ConLeche (eqA eqReflA eqRecA eqName eqReflName)

variable {m : EnvModel V env} {A : (Name → Nat) → Term}

/-! ## The two spines the block's types are built from -/

/-- `@Eq.{u} α a b`, read through the tower. -/
def eqSpine (ψ : Name → Nat) (i j k : Nat) : Term :=
  .app (.app (.app (eqValT ψ) (.bvar i)) (.bvar j)) (.bvar k)

/-- `@Eq.refl.{u} α a`, read through the tower. -/
def eqReflSpine (ψ : Name → Nat) (i j : Nat) : Term :=
  .app (.app (eqReflValT ψ) (.bvar i)) (.bvar j)

theorem eqSpine_interp {ψ : Name → Nat} {i j k : Nat} {ρ : Nat → V}
    {Aset a b : V} (hi : ρ i = Aset) (hj : ρ j = a) (hk : ρ k = b)
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset) (hb : b ∈ˢ Aset) :
    interp V ρ (eqSpine ψ i j k) = eqv a b ∧
      WellDenoted V ρ (eqSpine ψ i j k) ∧
      interp V ρ (eqSpine ψ i j k) ∈ˢ (univZero : V) := by
  have hAi : interp V ρ (Term.bvar i) = Aset := by
    rw [interp_bvar, hi]
  have haj : interp V ρ (Term.bvar j) = a := by
    rw [interp_bvar, hj]
  have hbk : interp V ρ (Term.bvar k) = b := by
    rw [interp_bvar, hk]
  obtain ⟨hok, hz⟩ := eqValT_app₃_okP ψ ρ (Aa := .bvar i) (la := .bvar j)
    (ra := .bvar k) trivial trivial
    trivial (by rw [hAi]; exact hA)
    (by rw [hAi, haj]; exact ha) (by rw [hAi, hbk]; exact hb)
  refine ⟨?_, hok, hz⟩
  rw [eqSpine, interp_app, interp_app, interp_app, hAi, haj, hbk,
    eqValT_app₃ ψ ρ Aset a b hA ha hb]

theorem eqReflSpine_data {ψ : Name → Nat} {i j : Nat} {ρ : Nat → V}
    {Aset a : V} (hi : ρ i = Aset) (hj : ρ j = a)
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset) :
    interp V ρ (eqReflSpine ψ i j) = (pt : V) ∧
      WellDenoted V ρ (eqReflSpine ψ i j) := by
  have hpt : interp V ρ (eqReflValT ψ) = (pt : V) :=
    eqReflValT_interp ψ ρ
  have hAi : interp V ρ (Term.bvar i) = Aset := by
    rw [interp_bvar, hi]
  have haj : interp V ρ (Term.bvar j) = a := by
    rw [interp_bvar, hj]
  have h1 := WellDenoted_app_pt (S := (univ (ψ uN) : V))
    (a := Term.bvar i) (eqReflValT_wellDenoted ψ ρ) hpt
    trivial (by rw [hAi]; exact hA)
  have h2 := WellDenoted_app_pt (S := Aset) (a := Term.bvar j)
    h1.1 h1.2 trivial (by rw [haj]; exact ha)
  exact ⟨h2.2, h2.1⟩

/-! ## `Eq` and `Eq.refl` -/

/-- `Eq`'s type reading. -/
@[expose] def eqTy (ψ : Name → Nat) : Term :=
  .pi (.sort (ψ uN)) (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))

/-- `Eq.refl`'s type reading: two binders over the spine. -/
def eqReflTy (ψ : Name → Nat) : Term :=
  .pi (.sort (ψ uN)) (.pi (.bvar 0) (eqSpine ψ 1 0 0))

/-- **`Eq`'s type reading.** -/
theorem denote_eqA_type {env' : Env}
    {acval : Name → (Name → Nat) → Term} (ψ : Name → Nat) :
    denote acval env' ψ 0 eqA.toConstantVal.type
      = some (eqTy ψ) := by
  simp [eqA, ConstantInfo.toConstantVal, denote_forallE, denote_sort,
    denote_fvar, Expr.instantiate1, eqTy, Level.eval, uN]

theorem eqTy_wellDenoted (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedTy V ρ (eqTy ψ) :=
  ⟨⟨trivial, IsTy_univ _, fun _ hA => ⟨trivial, IsTy_of_mem_univ hA,
      fun _ _ => ⟨trivial, IsTy_of_mem_univ hA,
      fun _ _ => trivial, fun _ _ => IsTy_univ 0⟩, fun _ _ => IsTy_piV⟩,
      fun _ _ => IsTy_piV⟩, IsTy_piV⟩

theorem eqTy_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqTy ψ)
      = piV (univ (ψ uN) : V)
          (fun a => piV a (fun _ => piV a (fun _ => univZero))) := by
  rw [eqTy, interp_pi, interp_sort]
  refine piV_congr fun a _ => ?_
  rw [interp_pi]
  simp only [interp_bvar, cons]
  refine piV_congr fun x _ => ?_
  rw [interp_pi]
  simp only [interp_bvar, interp_sort, cons]
  exact piV_congr fun _ _ => univ_zero

/-- **`Eq.refl`'s type reading.**  Stated at *any* extension whose
cons is not `Eq`, because `Eq.rec`'s row reads it as its fired
constructor's telescope. -/
theorem denote_eqReflTy {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = eqName)
    (hE : env.find? eqName = some eqA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValT ψ) :
    denote (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts, env.tables⟩ ψ 0
        eqReflA.toConstantVal.type
      = some (eqReflTy ψ) := by
  have hEc : ∀ d : Nat,
      denote (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts, env.tables⟩ ψ d
        (.const eqName [.param uN]) = some (eqValT ψ) := by
    intro d
    rw [denote_eqLeaf (m := m) (A := A) ψ (Level.param uN) hne hE d,
      show ([Level.param uN] : List Level)
        = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN], hEv]
  rw [show eqReflA.toConstantVal.type
      = Expr.forallE (.sort (.param uN))
          (Expr.forallE (.bvar 0)
            (.app (.app (.app (.const eqName [.param uN]) (.bvar 1))
              (.bvar 0)) (.bvar 0))) from rfl]
  simp [denote_forallE, denote_sort, denote_app, denote_fvar,
    Expr.instantiate1, eqReflTy, eqSpine, hEc,
    Level.eval]

theorem eqReflTy_data (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenoted V ρ (eqReflTy ψ) ∧
      interp V ρ (eqReflTy ψ)
        = piV (univ (ψ uN) : V) (fun a => piV a (fun x => eqv x x)) := by
  have hstep : ∀ Aset x : V, Aset ∈ˢ (univ (ψ uN) : V) → x ∈ˢ Aset →
      interp V (cons x (cons Aset ρ)) (eqSpine ψ 1 0 0) = eqv x x ∧
      WellDenoted V (cons x (cons Aset ρ)) (eqSpine ψ 1 0 0) ∧
      interp V (cons x (cons Aset ρ)) (eqSpine ψ 1 0 0)
        ∈ˢ (univZero : V) := by
    intro Aset x hA hx
    exact eqSpine_interp (ρ := cons x (cons Aset ρ))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA hx hx
  constructor
  · rw [eqReflTy]
    refine (WellDenoted_pi_zero (Aa := .sort (ψ uN)) trivial
      (IsTy_univ _) ?_ ?_).1
    all_goals (
      intro Aset hAset
      rw [interp_sort] at hAset
      have hlev := WellDenoted_pi_zero (Aa := Term.bvar 0)
        (ρ := cons Aset ρ) trivial
        (by simpa [interp_bvar, cons] using IsTy_of_mem_univ hAset)
        (fun x hx => (hstep Aset x hAset
          (by simpa [interp_bvar, cons] using hx)).2.1)
        (fun x hx => (hstep Aset x hAset
          (by simpa [interp_bvar, cons] using hx)).2.2))
    case _ => exact hlev.1
    case _ => exact hlev.2
  · rw [eqReflTy, interp_pi, interp_sort]
    refine piV_congr fun Aset hAset => ?_
    rw [interp_pi]
    simp only [interp_bvar, cons]
    exact piV_congr fun x hx => (hstep Aset x hAset hx).1

/-! ### The two installs -/

/-- **`Eq`, installed at the P tier** — the tier's one `eq_law`
bespoke cons. -/
theorem extendEq (mp : EnvModelM V μ env)
    (hfresh : env.find? eqName = none)
    (hwf : EnvWF ⟨eqA :: env.consts, env.tables⟩) :
    ∃ mp' : EnvModelM V μ ⟨eqA :: env.consts, env.tables⟩,
      mp'.base2.acval
        = acvalWith mp.base2.acval eqA.name eqValT ∧
      (LfpCover mp [] → LfpCover mp' [eqName]) := by
  refine coverA_pend hfresh <| declStep_preserves_of_basis_cons_eqrow mp (A := eqValT) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h) (by decide)
    (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf
      (fun ψ => by exact eqValT_closed ψ)
      rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT eqA.name ψ
          = none from rfl] at hp
        exact nomatch hp) (fun _ _ _ _ h => nomatch h))
    (fun ψ₁ ψ₂ hp => eqValT_congr
      (hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)))
    (fun ψ ρ => eqValT_wellDenoted ψ ρ)
    (fun ψ => ⟨_, denote_eqA_type ψ⟩) ?_ ?_ ?_
    (hind := indStrictHead_cons_prop
      (ab := fun ψ => [.sort (ψ uN), .bvar 0, .bvar 1])
      fun ψ => denote_eqA_type ψ)
  · intro ψ ta h ρ
    rw [denote_eqA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact eqTy_wellDenoted ψ ρ
  · intro ψ ta h ρ
    rw [denote_eqA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [eqTy_interp]
    exact eqValT_mem ψ ρ
  · intro m₂ hac
    refine eqLaw_of_tower m₂ fun ψ => ?_
    rw [hac, show eqName = eqA.name from rfl, acvalWith_self]

/-- **`Eq.refl`, installed at the P tier.** -/
theorem extendEqRefl (mp : EnvModelM V μ env)
    (hE : env.find? eqName = some eqA)
    (hEv : ∀ ψ : Name → Nat, mp.base2.acval eqName ψ = eqValT ψ)
    (hfresh : env.find? eqReflA.name = none)
    (hwf : EnvWF ⟨eqReflA :: env.consts, env.tables⟩) :
    ∃ mp' : EnvModelM V μ ⟨eqReflA :: env.consts, env.tables⟩,
      mp'.base2.acval
        = acvalWith mp.base2.acval eqReflA.name eqReflValT ∧
      (LfpCover mp [eqName] → LfpCover mp' [eqName]) := by
  have hty := fun ψ =>
    denote_eqReflTy (m := mp.base2) (A := eqReflValT) (c₀ := eqReflA)
      ψ (by decide) hE hEv
  refine coverA_cons hfresh (fun _ h => h) (fun _ _ h => nomatch h)
    (hhead := hhead_ctor (c₀ := eqReflA) rfl rfl rfl (Or.inl List.mem_cons_self)) <|
    declStep_preserves_of_basis_cons mp (A := eqReflValT) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf
      (fun ψ => by exact eqReflValT_closed ψ)
      rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT eqReflA.name ψ
          = none from rfl] at hp
        exact nomatch hp) (fun _ _ _ _ h => nomatch h))
    (fun ψ₁ ψ₂ hp => eqReflValT_congr
      (hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)))
    (fun ψ ρ => eqReflValT_wellDenoted ψ ρ)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact ⟨(eqReflTy_data ψ ρ).1, by rw [(eqReflTy_data ψ ρ).2]; exact IsTy_piV⟩
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [(eqReflTy_data ψ ρ).2]
    exact eqReflValT_mem ψ ρ

/-! ## `Eq.rec`

Its rule returns the minor premise, so the
only real content anywhere in the block is that the major premise's
membership forces `a = b` and the proof to be `pt`: an inhabitant of
`eqv a b` gives `a = b` by `eq_of_mem_eqv`, and `eqv` is a truth value, so
the inhabitant is the canonical proof by `mem_univ_zero`. -/

/-- `Eq.rec`'s motive binder domain reading. -/
def eqRecMotiveTy (ψ : Name → Nat) : Term :=
  .pi (.bvar 1) (.pi (eqSpine ψ 2 1 0) (.sort (ψ u1N)))

/-- `Eq.rec`'s minor binder domain reading. -/
def eqRecMinorTy (ψ : Name → Nat) : Term :=
  .app (.app (.bvar 0) (.bvar 1)) (eqReflSpine ψ 2 1)

/-- `Eq.rec`'s type reading. -/
def eqRecTy (ψ : Name → Nat) : Term :=
  .pi (.sort (ψ uN))
    (.pi (.bvar 0)
      (.pi (eqRecMotiveTy ψ)
        (.pi (eqRecMinorTy ψ)
          (.pi (.bvar 3)
            (.pi (eqSpine ψ 4 3 0)
              (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))))

/-- `Eq.rec`'s rule's RHS reading: the same four domains, over the
minor premise. -/
def eqRecRa (ψ : Name → Nat) : Term :=
  .lam (.sort (ψ uN))
    (.lam (.bvar 0)
      (.lam (eqRecMotiveTy ψ)
        (.lam (eqRecMinorTy ψ) (.bvar 0))))

/-- The motive space: `∀ b, a = b → Sort u₁`. -/
noncomputable def eqRecMotiveSpace (V : Type w) [SetTheory V]
    (u1 : Nat) (Aset a : V) : V :=
  piV Aset fun b => piV (eqv a b) fun _ => (univ u1 : V)

theorem eqRecMotiveTy_data {ψ : Name → Nat} {Aset a : V}
    (ρ : Nat → V) (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset) :
    interp V (cons a (cons Aset ρ)) (eqRecMotiveTy ψ)
        = eqRecMotiveSpace V (ψ u1N) Aset a ∧
      WellDenotedTy V (cons a (cons Aset ρ)) (eqRecMotiveTy ψ) := by
  have hsp : ∀ b : V, b ∈ˢ Aset →
      interp V (cons b (cons a (cons Aset ρ))) (eqSpine ψ 2 1 0)
          = eqv a b ∧
        WellDenoted V (cons b (cons a (cons Aset ρ))) (eqSpine ψ 2 1 0) ∧
        interp V (cons b (cons a (cons Aset ρ))) (eqSpine ψ 2 1 0)
          ∈ˢ (univZero : V) := fun b hb =>
    eqSpine_interp (ρ := cons b (cons a (cons Aset ρ)))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA ha hb
  have hdom : interp V (cons a (cons Aset ρ)) (Term.bvar 1)
      = Aset := by simp [interp_bvar, cons]
  refine ⟨?_, ?_⟩
  · rw [eqRecMotiveTy, interp_pi, eqRecMotiveSpace, hdom]
    refine piV_congr fun b hb => ?_
    rw [interp_pi, (hsp b hb).1]
    exact piV_congr fun _ _ => interp_sort V _ _
  · refine ⟨⟨trivial, by rw [hdom]; exact IsTy_of_mem_univ hA, fun b hb => ?_,
        fun _ _ => IsTy_piV⟩, IsTy_piV⟩
    rw [hdom] at hb
    exact ⟨(hsp b hb).2.1, Or.inl (hsp b hb).2.2, fun _ _ => trivial,
      fun _ _ => IsTy_univ _⟩

theorem eqRecMinorTy_data {ψ : Name → Nat} {Aset a M : V}
    (ρ : Nat → V) (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset)
    (hM : M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a) :
    interp V (cons M (cons a (cons Aset ρ))) (eqRecMinorTy ψ)
        = app (app M a) pt ∧
      WellDenotedTy V (cons M (cons a (cons Aset ρ))) (eqRecMinorTy ψ) ∧
      app (app M a) pt ∈ˢ (univ (ψ u1N) : V) := by
  obtain ⟨hrint, hrok⟩ := eqReflSpine_data (ψ := ψ) (i := 2) (j := 1)
    (ρ := cons M (cons a (cons Aset ρ)))
    (by simp [cons]) (by simp [cons]) hA ha
  have hM0 : M ∈ˢ piV Aset (fun b => piV (eqv a b)
      fun _ => (univ (ψ u1N) : V)) := hM
  have hMa : app M a ∈ˢ piV (eqv a a) fun _ => (univ (ψ u1N) : V) :=
    app_mem_piV hM0 ha
  have hMap : app (app M a) pt ∈ˢ (univ (ψ u1N) : V) :=
    app_mem_piV hMa (pt_mem_eqv_self a)
  have hMb : interp V (cons M (cons a (cons Aset ρ)))
      (Term.bvar 0) = M := by simp [interp_bvar, cons]
  have hab : interp V (cons M (cons a (cons Aset ρ)))
      (Term.bvar 1) = a := by simp [interp_bvar, cons]
  have hint : interp V (cons M (cons a (cons Aset ρ))) (eqRecMinorTy ψ)
      = app (app M a) pt := by
    rw [eqRecMinorTy, interp_app, interp_app, hrint, hMb, hab]
  refine ⟨hint, ⟨?_, by rw [hint]; exact IsTy_of_mem_univ hMap⟩, hMap⟩
  rw [eqRecMinorTy, WellDenoted_app]
  refine ⟨?_, hrok, slot_of_mem_piV V (by rw [interp_app, hMb, hab]; exact hMa)
    (by rw [hrint]; exact pt_mem_eqv_self a) (IsTy_eqv a a)⟩
  rw [WellDenoted_app]
  exact ⟨trivial, trivial, slot_of_mem_piV V (by rw [hMb]; exact hM0)
    (by rw [hab]; exact ha) (IsTy_of_mem_univ hA)⟩

/-- **The major premise collapses the block**: an inhabitant of
`eqv a b` identifies `a` with `b` and is itself the canonical proof.
This is `Eq.rec`'s entire iota content. -/
theorem eqRec_major_collapse {a b h : V} (hh : h ∈ˢ eqv a b) :
    a = b ∧ h = pt :=
  ⟨eq_of_mem_eqv hh, mem_univ_zero (univ_zero (V := V) ▸ eqv_mem_univZero a b) hh⟩

/-! ### The tower, spelled as the walk reads it -/

/-- The tower with the reading's own binder domains. -/
def eqRecRaTower (ψ : Name → Nat) : Term :=
  .lam (.sort (ψ uN))
    (.lam (.bvar 0)
      (.lam (eqRecMotiveTy ψ)
        (.lam (eqRecMinorTy ψ)
          (.lam (.bvar 3)
            (.lam (eqSpine ψ 4 3 0) (.bvar 2))))))

/-- The walk's spelling is the stored tower. -/
theorem eqRecRaTower_eq (ψ : Name → Nat) : eqRecRaTower ψ = eqRecValT ψ := by rfl

/-- **`Eq.rec`'s tower is graded and inhabits its type's reading** —
in one walk (`WellDenoted_lam_piV` six times).  The only content is at the bottom:
the major premise collapses `b` onto `a` and itself onto `pt`, and the
minor premise is already there. -/
theorem eqRecRaTower_data (ψ : Name → Nat)
    (ρ : Nat → V) :
    WellDenoted V ρ (eqRecRaTower ψ) ∧
      interp V ρ (eqRecRaTower ψ)
        ∈ˢ interp V ρ (eqRecTy ψ) := by
  -- level 6: the body, at a fixed major premise
  have h6 : ∀ Aset a M mn bb : V, Aset ∈ˢ (univ (ψ uN) : V) →
      a ∈ˢ Aset → M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      mn ∈ˢ app (app M a) pt → bb ∈ˢ Aset →
      WellDenoted V (cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
          (.lam (eqSpine ψ 4 3 0) (.bvar 2)) ∧
        interp V (cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
            (.lam (eqSpine ψ 4 3 0) (.bvar 2))
          ∈ˢ piV (eqv a bb) (fun h => app (app M bb) h) := by
    intro Aset a M mn bb hA ha hM hmn hbb
    obtain ⟨hsint, hsok, -⟩ := eqSpine_interp
      (ρ := cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
      (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA ha hbb
    have hM0 : M ∈ˢ piV Aset (fun x => piV (eqv a x)
        fun _ => (univ (ψ u1N) : V)) := hM
    have hMb : app M bb ∈ˢ piV (eqv a bb)
        fun _ => (univ (ψ u1N) : V) :=
      app_mem_piV hM0 hbb
    have key : ∀ h : V, h ∈ˢ eqv a bb →
        app (app M bb) h = app (app M a) pt ∧
          app (app M bb) h ∈ˢ (univ (ψ u1N) : V) := by
      intro h hh
      obtain ⟨hab, hpt⟩ := eqRec_major_collapse (V := V) hh
      refine ⟨by rw [hab, hpt], ?_⟩
      exact app_mem_piV hMb hh
    have hstep := WellDenoted_lam_piV (V := V)
      (Aa := eqSpine ψ 4 3 0) (bd := .bvar 2)
      (F := fun h => app (app M bb) h) hsok (by rw [hsint]; exact IsTy_eqv _ _)
      (fun h hh => by
        rw [hsint] at hh
        refine ⟨trivial, ?_⟩
        rw [show interp V (cons h (cons bb (cons mn (cons M
            (cons a (cons Aset ρ)))))) (Term.bvar 2) = mn
          from by simp [interp_bvar, cons], (key h hh).1]
        exact hmn)
      (fun h hh => by rw [hsint] at hh; exact IsTy_of_mem_univ (key h hh).2)
    rw [hsint] at hstep
    exact hstep
  -- level 5
  have h5 : ∀ Aset a M mn : V, Aset ∈ˢ (univ (ψ uN) : V) →
      a ∈ˢ Aset → M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      mn ∈ˢ app (app M a) pt →
      WellDenoted V (cons mn (cons M (cons a (cons Aset ρ))))
          (.lam (.bvar 3) (.lam (eqSpine ψ 4 3 0) (.bvar 2))) ∧
        interp V (cons mn (cons M (cons a (cons Aset ρ))))
            (.lam (.bvar 3) (.lam (eqSpine ψ 4 3 0) (.bvar 2)))
          ∈ˢ piV Aset
            (fun bb => piV (eqv a bb) fun h => app (app M bb) h) := by
    intro Aset a M mn hA ha hM hmn
    have hdom : interp V (cons mn (cons M (cons a (cons Aset ρ))))
        (Term.bvar 3) = Aset := by simp [interp_bvar, cons]
    have hstep := WellDenoted_lam_piV (V := V)
      (Aa := Term.bvar 3)
      (bd := .lam (eqSpine ψ 4 3 0) (.bvar 2))
      (F := fun bb => piV (eqv a bb) fun h => app (app M bb) h)
      trivial (by rw [hdom]; exact IsTy_of_mem_univ hA)
      (fun bb hbb => h6 Aset a M mn bb hA ha hM hmn
        (by rwa [hdom] at hbb))
      (fun _ _ => IsTy_piV)
    rw [hdom] at hstep
    exact hstep
  -- level 4
  have h4 : ∀ Aset a M : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      WellDenoted V (cons M (cons a (cons Aset ρ)))
          (.lam (eqRecMinorTy ψ)
            (.lam (.bvar 3)
              (.lam (eqSpine ψ 4 3 0) (.bvar 2)))) ∧
        interp V (cons M (cons a (cons Aset ρ)))
            (.lam (eqRecMinorTy ψ)
              (.lam (.bvar 3)
                (.lam (eqSpine ψ 4 3 0) (.bvar 2))))
          ∈ˢ piV (app (app M a) pt) (fun _ => piV Aset
            (fun bb => piV (eqv a bb) fun h => app (app M bb) h)) := by
    intro Aset a M hA ha hM
    obtain ⟨hmint, hmok, -⟩ := eqRecMinorTy_data ρ hA ha hM
    have hstep := WellDenoted_lam_piV (V := V)
      (Aa := eqRecMinorTy ψ)
      (F := fun _ => piV Aset
        (fun bb => piV (eqv a bb) fun h => app (app M bb) h))
      hmok.1 hmok.2
      (fun mn hmn => h5 Aset a M mn hA ha hM (by rwa [hmint] at hmn))
      (fun _ _ => IsTy_piV)
    rw [hmint] at hstep
    exact hstep
  -- level 3
  have h3 : ∀ Aset a : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      WellDenoted V (cons a (cons Aset ρ))
          (.lam (eqRecMotiveTy ψ)
            (.lam (eqRecMinorTy ψ)
              (.lam (.bvar 3)
                (.lam (eqSpine ψ 4 3 0) (.bvar 2))))) ∧
        interp V (cons a (cons Aset ρ))
            (.lam (eqRecMotiveTy ψ)
              (.lam (eqRecMinorTy ψ)
                (.lam (.bvar 3)
                  (.lam (eqSpine ψ 4 3 0) (.bvar 2)))))
          ∈ˢ piV (eqRecMotiveSpace V (ψ u1N) Aset a)
            (fun M => piV (app (app M a) pt) (fun _ => piV Aset
              (fun bb => piV (eqv a bb)
                fun h => app (app M bb) h))) := by
    intro Aset a hA ha
    obtain ⟨hmint, hmok⟩ := eqRecMotiveTy_data ρ hA ha
    have hstep := WellDenoted_lam_piV (V := V)
      (Aa := eqRecMotiveTy ψ)
      (F := fun M => piV (app (app M a) pt) (fun _ => piV Aset
        (fun bb => piV (eqv a bb) fun h => app (app M bb) h)))
      hmok.1 hmok.2
      (fun M hM => h4 Aset a M hA ha (by rwa [hmint] at hM))
      (fun _ _ => IsTy_piV)
    rw [hmint] at hstep
    exact hstep
  -- level 2
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ (ψ uN) : V) →
      WellDenoted V (cons Aset ρ)
          (.lam (.bvar 0)
            (.lam (eqRecMotiveTy ψ)
              (.lam (eqRecMinorTy ψ)
                (.lam (.bvar 3)
                  (.lam (eqSpine ψ 4 3 0) (.bvar 2)))))) ∧
        interp V (cons Aset ρ)
            (.lam (.bvar 0)
              (.lam (eqRecMotiveTy ψ)
                (.lam (eqRecMinorTy ψ)
                  (.lam (.bvar 3)
                    (.lam (eqSpine ψ 4 3 0) (.bvar 2))))))
          ∈ˢ piV Aset (fun a =>
            piV (eqRecMotiveSpace V (ψ u1N) Aset a)
              (fun M => piV (app (app M a) pt) (fun _ => piV Aset
                (fun bb => piV (eqv a bb)
                  fun h => app (app M bb) h)))) := by
    intro Aset hA
    have hdom : interp V (cons Aset ρ) (Term.bvar 0) = Aset := by
      simp [interp_bvar, cons]
    have hstep := WellDenoted_lam_piV (V := V)
      (Aa := Term.bvar 0)
      (F := fun a => piV (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piV (app (app M a) pt) (fun _ => piV Aset
          (fun bb => piV (eqv a bb) fun h => app (app M bb) h))))
      trivial (by rw [hdom]; exact IsTy_of_mem_univ hA)
      (fun a ha => h3 Aset a hA (by rwa [hdom] at ha))
      (fun _ _ => IsTy_piV)
    rw [hdom] at hstep
    exact hstep
  have hstep := WellDenoted_lam_piV (V := V)
    (Aa := .sort (ψ uN))
    (F := fun Aset => piV Aset (fun a =>
      piV (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piV (app (app M a) pt) (fun _ => piV Aset
          (fun bb => piV (eqv a bb) fun h => app (app M bb) h)))))
    trivial (IsTy_univ _)
    (fun Aset hA => h2 Aset (by rwa [interp_sort] at hA))
    (fun _ _ => IsTy_piV)
  refine ⟨hstep.1, ?_⟩
  rw [interp_sort] at hstep
  refine (?_ : interp V ρ (eqRecTy ψ)
    = piV (univ (ψ uN) : V) (fun Aset => piV Aset (fun a =>
      piV (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piV (app (app M a) pt) (fun _ => piV Aset
          (fun bb => piV (eqv a bb)
            fun h => app (app M bb) h)))))) ▸ hstep.2
  -- the type reading's own six function spaces, in the same order
  rw [eqRecTy, interp_pi, interp_sort]
  refine piV_congr fun Aset hAset => ?_
  rw [interp_pi]
  simp only [interp_bvar, cons]
  refine piV_congr fun a ha => ?_
  rw [interp_pi, (eqRecMotiveTy_data ρ hAset ha).1]
  refine piV_congr fun M hM => ?_
  rw [interp_pi, (eqRecMinorTy_data ρ hAset ha hM).1]
  refine piV_congr fun mn _ => ?_
  rw [interp_pi]
  simp only [interp_bvar, cons]
  refine piV_congr fun bb hbb => ?_
  rw [interp_pi,
    (eqSpine_interp (ρ := cons bb (cons mn (cons M (cons a
        (cons Aset ρ))))) (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons])
      hAset ha hbb).1]
  refine piV_congr fun h _ => ?_
  simp [interp_app, interp_bvar, cons]

/-! ### The two readings -/

/-- **`Eq.rec`'s type reading.** -/
theorem denote_eqRecA_type (ψ : Name → Nat)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValT ψ)
    (hRv : ∀ ψ : Name → Nat, m.acval eqReflName ψ = eqReflValT ψ) :
    denote (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts, env.tables⟩ ψ 0 eqRecA.toConstantVal.type
      = some (eqRecTy ψ) := by
  have hEc : ∀ d : Nat,
      denote (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts, env.tables⟩ ψ d (.const eqName [.param uN])
        = some (eqValT ψ) := by
    intro d
    rw [denote_eqLeaf (m := m) (A := A) ψ (Level.param uN)
        (by decide) hE d,
      show ([Level.param uN] : List Level)
        = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN], hEv]
  have hRc : ∀ d : Nat,
      denote (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts, env.tables⟩ ψ d (.const eqReflName [.param uN])
        = some (eqReflValT ψ) := by
    intro d
    have hf' : (⟨eqRecA :: env.consts, env.tables⟩ : Env).find? eqReflName
        = some eqReflA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hR
    rw [denote_const hf' (by rfl), acvalWith_ne (by decide),
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
                  (.sort (.param u1N))))
              (Expr.forallE
                (.app (.app (.bvar 0) (.bvar 1))
                  (.app (.app (.const eqReflName [.param uN])
                    (.bvar 2)) (.bvar 1)))
                (Expr.forallE (.bvar 3)
                  (Expr.forallE
                    (.app (.app (.app (.const eqName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 0))
                    (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))))) from rfl]
  simp [denote_forallE, denote_sort, denote_app, denote_fvar,
    Expr.instantiate1, eqRecTy, eqRecMotiveTy, eqRecMinorTy,
    eqSpine, eqReflSpine, hEc, hRc, Level.eval]

/-- **`Eq.rec`'s rule's RHS reading.** -/
theorem denote_eqRec_rhs (ψ : Name → Nat)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValT ψ)
    (hRv : ∀ ψ : Name → Nat, m.acval eqReflName ψ = eqReflValT ψ) :
    denote (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts, env.tables⟩ ψ 0 eqRecRule.rhs
      = some (eqRecRa ψ) := by
  have hEc : ∀ d : Nat,
      denote (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts, env.tables⟩ ψ d (.const eqName [.param uN])
        = some (eqValT ψ) := by
    intro d
    rw [denote_eqLeaf (m := m) (A := A) ψ (Level.param uN)
        (by decide) hE d,
      show ([Level.param uN] : List Level)
        = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN], hEv]
  have hRc : ∀ d : Nat,
      denote (acvalWith m.acval eqRecA.name A)
        ⟨eqRecA :: env.consts, env.tables⟩ ψ d (.const eqReflName [.param uN])
        = some (eqReflValT ψ) := by
    intro d
    have hf' : (⟨eqRecA :: env.consts, env.tables⟩ : Env).find? eqReflName
        = some eqReflA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hR
    rw [denote_const hf' (by rfl), acvalWith_ne (by decide),
      show Level.substFn ψ eqReflA.toConstantVal.levelParams
        [Level.param uN] = Level.substFn ψ [uN]
          (List.map Level.param [uN]) from rfl,
      Level.substFn_param_self ψ [uN], hRv]
  simp only [eqRecRule]
  simp [denote_lam, denote_forallE, denote_sort, denote_app,
    denote_fvar, Expr.instantiate1, eqRecRa, eqRecMotiveTy,
    eqRecMinorTy, eqSpine, eqReflSpine, hEc, hRc,
    Level.eval]

/-! ### The RHS tower and the two firing sides -/

/-- The function space the RHS tower inhabits. -/
noncomputable def eqRecRaSpace (V : Type w) [SetTheory V]
    (u u1 : Nat) : V :=
  piV (univ u : V) fun Aset => piV Aset fun a =>
    piV (eqRecMotiveSpace V u1 Aset a) fun M =>
      piV (app (app M a) pt) fun _ => app (app M a) pt

theorem eqRecRa_data (ψ : Name → Nat)
    (ρ : Nat → V) :
    WellDenoted V ρ (eqRecRa ψ) ∧
      interp V ρ (eqRecRa ψ)
        ∈ˢ eqRecRaSpace V (ψ uN) (ψ u1N) := by
  have h4 : ∀ Aset a M : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      WellDenoted V (cons M (cons a (cons Aset ρ)))
          (.lam (eqRecMinorTy ψ) (.bvar 0)) ∧
        interp V (cons M (cons a (cons Aset ρ)))
            (.lam (eqRecMinorTy ψ) (.bvar 0))
          ∈ˢ piV (app (app M a) pt) (fun _ => app (app M a) pt) := by
    intro Aset a M hA ha hM
    obtain ⟨hmint, hmok, hmuniv⟩ := eqRecMinorTy_data ρ hA ha hM
    have hstep := WellDenoted_lam_piV (V := V)
      (Aa := eqRecMinorTy ψ) (bd := .bvar 0)
      (F := fun _ => app (app M a) pt) hmok.1 hmok.2
      (fun mn hmn => by
        rw [hmint] at hmn
        exact ⟨trivial, by
          rw [show interp V (cons mn (cons M (cons a (cons Aset ρ))))
            (Term.bvar 0) = mn from by simp [interp_bvar, cons]]
          exact hmn⟩)
      (fun _ _ => IsTy_of_mem_univ hmuniv)
    rw [hmint] at hstep
    exact hstep
  have h3 : ∀ Aset a : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      WellDenoted V (cons a (cons Aset ρ))
          (.lam (eqRecMotiveTy ψ)
            (.lam (eqRecMinorTy ψ) (.bvar 0))) ∧
        interp V (cons a (cons Aset ρ))
            (.lam (eqRecMotiveTy ψ)
              (.lam (eqRecMinorTy ψ) (.bvar 0)))
          ∈ˢ piV (eqRecMotiveSpace V (ψ u1N) Aset a)
            (fun M => piV (app (app M a) pt)
              (fun _ => app (app M a) pt)) := by
    intro Aset a hA ha
    obtain ⟨hmint, hmok⟩ := eqRecMotiveTy_data ρ hA ha
    have hstep := WellDenoted_lam_piV (V := V)
      (Aa := eqRecMotiveTy ψ)
      (F := fun M => piV (app (app M a) pt)
        (fun _ => app (app M a) pt)) hmok.1 hmok.2
      (fun M hM => h4 Aset a M hA ha (by rwa [hmint] at hM))
      (fun _ _ => IsTy_piV)
    rw [hmint] at hstep
    exact hstep
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ (ψ uN) : V) →
      WellDenoted V (cons Aset ρ)
          (.lam (.bvar 0) (.lam (eqRecMotiveTy ψ)
            (.lam (eqRecMinorTy ψ) (.bvar 0)))) ∧
        interp V (cons Aset ρ)
            (.lam (.bvar 0) (.lam (eqRecMotiveTy ψ)
              (.lam (eqRecMinorTy ψ) (.bvar 0))))
          ∈ˢ piV Aset (fun a =>
            piV (eqRecMotiveSpace V (ψ u1N) Aset a)
              (fun M => piV (app (app M a) pt)
                (fun _ => app (app M a) pt))) := by
    intro Aset hA
    have hdom : interp V (cons Aset ρ) (Term.bvar 0) = Aset := by
      simp [interp_bvar, cons]
    have hstep := WellDenoted_lam_piV (V := V)
      (Aa := Term.bvar 0)
      (F := fun a => piV (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piV (app (app M a) pt)
          (fun _ => app (app M a) pt)))
      trivial (by rw [hdom]; exact IsTy_of_mem_univ hA)
      (fun a ha => h3 Aset a hA (by rwa [hdom] at ha))
      (fun _ _ => IsTy_piV)
    rw [hdom] at hstep
    exact hstep
  have hstep := WellDenoted_lam_piV (V := V)
    (Aa := .sort (ψ uN))
    (F := fun Aset => piV Aset (fun a =>
      piV (eqRecMotiveSpace V (ψ u1N) Aset a)
        (fun M => piV (app (app M a) pt)
          (fun _ => app (app M a) pt))))
    trivial (IsTy_univ _)
    (fun Aset hA => h2 Aset (by rwa [interp_sort] at hA))
    (fun _ _ => IsTy_piV)
  rw [interp_sort] at hstep
  exact ⟨hstep.1, hstep.2⟩

/-- **`Eq.rec`'s recursor tower fires to the minor premise**: six
`app_lamV`, each on its domain. -/
theorem eqRecRaTower_app₆ (ψ : Name → Nat) (ρ : Nat → V) {Aset a M mn bb h : V}
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset)
    (hM : M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a)
    (hmn : mn ∈ˢ app (app M a) pt) (hbb : bb ∈ˢ Aset)
    (hh : h ∈ˢ eqv a bb) :
    app (app (app (app (app (app
        (interp V ρ (eqRecRaTower ψ)) Aset) a) M) mn) bb) h = mn := by
  obtain ⟨hmint, -, -⟩ := eqRecMinorTy_data ρ hA ha hM
  obtain ⟨hmoint, -⟩ := eqRecMotiveTy_data ρ hA ha
  obtain ⟨hsint, -, -⟩ := eqSpine_interp
    (ρ := cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
    (i := 4) (j := 3) (k := 0)
    (by simp [cons]) (by simp [cons]) (by simp [cons]) hA ha hbb
  rw [eqRecRaTower, interp_lam, interp_sort, app_lamV hA,
    interp_lam,
    show interp V (cons Aset ρ) (Term.bvar 0) = Aset
      from by simp [interp_bvar, cons],
    app_lamV ha,
    interp_lam, hmoint, app_lamV hM,
    interp_lam, hmint, app_lamV hmn,
    interp_lam,
    show interp V (cons mn (cons M (cons a (cons Aset ρ))))
      (Term.bvar 3) = Aset from by simp [interp_bvar, cons],
    app_lamV hbb,
    interp_lam, hsint, app_lamV hh]
  simp [interp_bvar, cons]

/-- …and the RHS tower's four-fold application is the same value. -/
theorem eqRecRa_app₄ (ψ : Name → Nat) (ρ : Nat → V) {Aset a M mn : V}
    (hA : Aset ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ Aset)
    (hM : M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a)
    (hmn : mn ∈ˢ app (app M a) pt) :
    app (app (app (app (interp V ρ (eqRecRa ψ)) Aset) a) M) mn
      = mn := by
  obtain ⟨hmint, -, -⟩ := eqRecMinorTy_data ρ hA ha hM
  obtain ⟨hmoint, -⟩ := eqRecMotiveTy_data ρ hA ha
  rw [eqRecRa, interp_lam, interp_sort, app_lamV hA,
    interp_lam,
    show interp V (cons Aset ρ) (Term.bvar 0) = Aset
      from by simp [interp_bvar, cons],
    app_lamV ha,
    interp_lam, hmoint, app_lamV hM,
    interp_lam, hmint, app_lamV hmn]
  simp [interp_bvar, cons]

/-! ### The row -/

theorem eqRecValT_congr {ψ₁ ψ₂ : Name → Nat} (hu : ψ₁ uN = ψ₂ uN)
    (hu1 : ψ₁ u1N = ψ₂ u1N) : eqRecValT ψ₁ = eqRecValT ψ₂ := by
  rw [eqRecValT, eqRecValT, hu, hu1, eqValT_congr hu,
    eqReflValT_congr hu]

set_option maxHeartbeats 1000000 in
/-- **`Eq.rec`'s ι facts.**  The rule is K (`Eq.refl` has no
fields): at ANY major in the major's domain `eqv a b` the recursor
fires to the minor premise (`eqRecRaTower_app₆` against
`eqRecRa_app₄`, which never look at the major's value), and the
transport is the row's four `WellDenoted_app_fibre` steps.
`Eq.refl` binds two parameters; (S)/(P)/(U) concern rules that are not
K and are vacuous. -/
theorem eqRecExtra {m : EnvModel V env}
    (m₂ : EnvModel V ⟨eqRecA :: env.consts, env.tables⟩)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValT ψ)
    (hRv : ∀ ψ : Name → Nat, m.acval eqReflName ψ = eqReflValT ψ)
    (hac : m₂.acval = acvalWith m.acval eqRecA.name eqRecValT)
    (φ : Name → Nat) :
    RecRuleExtra m₂ φ eqRecA.name eqRecA.toConstantVal 5 4
      eqRecRule := by
  intro us _ TVa hTVa
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ eqRecA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  have hRa : denote m₂.acval ⟨eqRecA :: env.consts, env.tables⟩ φ 0
      (eqRecRule.rhs.instantiateLevelParams
        eqRecA.toConstantVal.levelParams us)
      = some (eqRecRa ψ) := by
    rw [denote_instLevels m₂.acval_params φ, hac, hψ,
      denote_eqRec_rhs (m := m) _ hE hR hEv hRv]
  have hTyRead : denote m₂.acval ⟨eqRecA :: env.consts, env.tables⟩ φ 0
      (eqRecA.toConstantVal.type.instantiateLevelParams
        eqRecA.toConstantVal.levelParams us)
      = some (eqRecTy ψ) := by
    rw [denote_instLevels m₂.acval_params φ, hac, hψ,
      denote_eqRecA_type (m := m) _ hE hR hEv hRv]
  obtain rfl : TVa = _ :=
    (Option.some.inj (hTyRead.symm.trans hTVa)).symm
  have hrecL : m₂.acval eqRecA.name
      (Level.substFn φ eqRecA.toConstantVal.levelParams us)
      = eqRecValT ψ := by
    rw [hac, acvalWith_self, hψ]
  have hR' : (⟨eqRecA :: env.consts, env.tables⟩ : Env).find? eqReflName
      = some eqReflA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hR
  refine ⟨fun _ => ⟨rfl, fun Ra hRa' ρ xs a restR hxs hfitR _ => ?_⟩,
    fun cvj cnP cnF hfj => ?_⟩
  · obtain rfl : Ra = _ := (Option.some.inj (hRa'.symm.trans hRa))
    obtain ⟨x1, x2, x3, x4, x5, rfl⟩ :
        ∃ p q r s t, xs = [p, q, r, s, t] := by
      match xs, hxs with
      | [p, q, r, s, t], _ => exact ⟨p, q, r, s, t, rfl⟩
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
    refine ⟨?_, ?_⟩
    · -- the fired equality: both sides are the minor premise
      simp only [List.take, List.cons_append, List.nil_append,
        Term.mkAppN_cons, Term.mkAppN_nil, hrecL, interp_app]
      rw [← eqRecRaTower_eq ψ,
        eqRecRaTower_app₆ ψ ρ f1 f2 f3 f4 f5 f6,
        eqRecRa_app₄ ψ ρ f1 f2 f3 f4]
    · -- the transport
      intro hxsA
      simp only [List.take, Term.mkAppN_cons, Term.mkAppN_nil]
      have hRm := (eqRecRa_data ψ ρ).2
      rw [eqRecRaSpace] at hRm
      have h1 := WellDenoted_app_fibre ((eqRecRa_data ψ ρ).1)
        (hxsA x1 (by simp)) hRm f1
        (IsTy_univ _)
      have h2 := WellDenoted_app_fibre h1.1 (hxsA x2 (by simp)) h1.2 f2
        (IsTy_of_mem_univ f1)
      have h3 := WellDenoted_app_fibre h2.1 (hxsA x3 (by simp)) h2.2 f3
        IsTy_piV
      exact (WellDenoted_app_fibre h3.1 (hxsA x4 (by simp)) h3.2 f4
        (IsTy_of_mem_univ (eqRecMinorTy_data ρ f1 f2 f3).2.2)).1
  · rw [show RecRule.ctor eqRecRule = eqReflName from rfl, hR'] at hfj
    obtain rfl : cvj = eqReflA.toConstantVal := by
      injection Option.some.inj hfj with a1 _ _
      exact a1.symm
    exact ⟨rfl, fun h => (nomatch h)⟩

set_option maxHeartbeats 1000000 in
/-- **`Eq.rec`'s `RecRuleLaw` row.**  The rule is `.plain`, so both
`.nested` conjuncts are `nomatch`; the fired equality is the minor
premise on both sides (`eqRecRaTower_app₆` against `eqRecRa_app₄`),
and the transport is four `WellDenoted_app_fibre` steps. -/
theorem eqRecLaw {m : EnvModel V env}
    (m₂ : EnvModel V ⟨eqRecA :: env.consts, env.tables⟩)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValT ψ)
    (hRv : ∀ ψ : Name → Nat, m.acval eqReflName ψ = eqReflValT ψ)
    (hac : m₂.acval = acvalWith m.acval eqRecA.name eqRecValT)
    (φ : Name → Nat) :
    RecRuleLaw m₂ φ eqRecA.name eqRecA.toConstantVal 5 4
      eqRecRule := by
  refine ⟨by decide, fun us hus => ?_,
    eqRecExtra (m := m) m₂ hE hR hEv hRv hac φ⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ eqRecA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  have hRa : denote m₂.acval ⟨eqRecA :: env.consts, env.tables⟩ φ 0
      (eqRecRule.rhs.instantiateLevelParams
        eqRecA.toConstantVal.levelParams us)
      = some (eqRecRa ψ) := by
    rw [denote_instLevels m₂.acval_params φ, hac, hψ,
      denote_eqRec_rhs (m := m) _ hE hR hEv hRv]
  refine ⟨_, hRa, fun ρ => (eqRecRa_data ψ ρ).1, ?_, ?_⟩
  · intro _ _ h
    exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev _ hpin hTVa hTVja hfitR hfitC
  have hR' : (⟨eqRecA :: env.consts, env.tables⟩ : Env).find? eqReflName
      = some eqReflA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hR
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
  have hTyRead : denote m₂.acval ⟨eqRecA :: env.consts, env.tables⟩ φ 0
      (eqRecA.toConstantVal.type.instantiateLevelParams
        eqRecA.toConstantVal.levelParams us)
      = some (eqRecTy ψ) := by
    rw [denote_instLevels m₂.acval_params φ, hac, hψ,
      denote_eqRecA_type (m := m) _ hE hR hEv hRv]
  obtain rfl : TVa = _ :=
    (Option.some.inj (hTyRead.symm.trans hTVa)).symm
  have hCtorRead : denote m₂.acval ⟨eqRecA :: env.consts, env.tables⟩ φ 0
      (eqReflA.toConstantVal.type.instantiateLevelParams
        eqReflA.toConstantVal.levelParams usj)
      = some (eqReflTy
          (Level.substFn φ eqReflA.toConstantVal.levelParams usj)) := by
    rw [denote_instLevels m₂.acval_params φ, hac,
      denote_eqReflTy (m := m) _ (by decide) hE hEv]
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
      = eqRecValT ψ := by
    rw [hac, acvalWith_self, hψ]
  have hctorL : m₂.acval eqReflName
      (Level.substFn φ eqReflA.toConstantVal.levelParams usj)
      = eqReflValT
        (Level.substFn φ eqReflA.toConstantVal.levelParams usj) := by
    rw [hac, acvalWith_ne (by decide), hRv]
  simp only [show RecRule.ctor eqRecRule = eqReflName from rfl,
    Term.mkAppN_cons, Term.mkAppN_nil, interp_app, hctorL,
    eqReflValT_interp, app_pt] at f6
  refine ⟨?_, ?_⟩
  · -- the fired equality
    simp only [show RecRule.ctor eqRecRule = eqReflName from rfl,
      show eqRecRule.ctorParams = 2 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      List.append_nil, Term.mkAppN_cons, Term.mkAppN_nil, hrecL,
      interp_app, hctorL, eqReflValT_interp, app_pt]
    rw [← eqRecRaTower_eq ψ,
      eqRecRaTower_app₆ ψ ρ f1 f2 f3 f4 f5 f6,
      eqRecRa_app₄ ψ ρ f1 f2 f3 f4]
  · -- the transport
    intro hxsA _
    simp only [show eqRecRule.ctorParams = 2 from rfl,
      List.take, List.drop, List.append_nil,
      Term.mkAppN_cons, Term.mkAppN_nil]
    have hRm := (eqRecRa_data ψ ρ).2
    rw [eqRecRaSpace] at hRm
    have h1 := WellDenoted_app_fibre ((eqRecRa_data ψ ρ).1)
      (hxsA x1 (by simp)) hRm f1
      (IsTy_univ _)
    have h2 := WellDenoted_app_fibre h1.1 (hxsA x2 (by simp)) h1.2 f2
      (IsTy_of_mem_univ f1)
    have h3 := WellDenoted_app_fibre h2.1 (hxsA x3 (by simp)) h2.2 f3
      IsTy_piV
    exact (WellDenoted_app_fibre h3.1 (hxsA x4 (by simp)) h3.2 f4
      (IsTy_of_mem_univ (eqRecMinorTy_data ρ f1 f2 f3).2.2)).1

/-- **`Eq.rec`'s type reading is graded** — six `WellDenoted_pi_of`
steps; the innermost body is the motive applied to the major premise,
a member of a universe. -/
theorem eqRecTy_wellDenoted (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedTy V ρ (eqRecTy ψ) := by
  have h6 : ∀ Aset a M mn bb : V, Aset ∈ˢ (univ (ψ uN) : V) →
      a ∈ˢ Aset → M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      bb ∈ˢ Aset →
      WellDenoted V (cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
        (.pi (eqSpine ψ 4 3 0)
          (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))) := by
    intro Aset a M mn bb hA ha hM hbb
    obtain ⟨hsint, hsok, -⟩ := eqSpine_interp
      (ρ := cons bb (cons mn (cons M (cons a (cons Aset ρ)))))
      (i := 4) (j := 3) (k := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA ha hbb
    have hM0 : M ∈ˢ piV Aset (fun x => piV (eqv a x)
        fun _ => (univ (ψ u1N) : V)) := hM
    have hMb : app M bb ∈ˢ piV (eqv a bb)
        fun _ => (univ (ψ u1N) : V) :=
      app_mem_piV hM0 hbb
    have hcodI : ∀ h : V, h ∈ˢ eqv a bb →
        interp V (cons h (cons bb (cons mn (cons M (cons a (cons Aset ρ))))))
          (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) = app (app M bb) h := by
      intro h _; simp [interp_app, interp_bvar, cons]
    have hM3 : ∀ h : V, interp V (cons h (cons bb (cons mn (cons M
        (cons a (cons Aset ρ)))))) (Term.bvar 3) = M := fun h => by
      simp [interp_bvar, cons]
    have hb1 : ∀ h : V, interp V (cons h (cons bb (cons mn (cons M
        (cons a (cons Aset ρ)))))) (Term.bvar 1) = bb := fun h => by
      simp [interp_bvar, cons]
    have hh0 : ∀ h : V, interp V (cons h (cons bb (cons mn (cons M
        (cons a (cons Aset ρ)))))) (Term.bvar 0) = h := fun h => by
      simp [interp_bvar, cons]
    refine WellDenoted_pi_of hsok (by rw [hsint]; exact IsTy_eqv _ _) (fun h hh => ?_)
      (fun h hh => by
        rw [hsint] at hh
        rw [hcodI h hh]
        exact IsTy_of_mem_univ (app_mem_piV hMb hh))
    rw [hsint] at hh
    rw [WellDenoted_app]
    refine ⟨?_, trivial, slot_of_mem_piV V (by rw [interp_app, hM3, hb1]; exact hMb)
      (by rw [hh0]; exact hh) (IsTy_eqv a bb)⟩
    rw [WellDenoted_app]
    exact ⟨trivial, trivial, slot_of_mem_piV V (by rw [hM3]; exact hM0)
      (by rw [hb1]; exact hbb) (IsTy_of_mem_univ hA)⟩
  have h5 : ∀ Aset a M mn : V, Aset ∈ˢ (univ (ψ uN) : V) →
      a ∈ˢ Aset → M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      WellDenoted V (cons mn (cons M (cons a (cons Aset ρ))))
        (.pi (.bvar 3) (.pi (eqSpine ψ 4 3 0)
          (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))) := by
    intro Aset a M mn hA ha hM
    have hdom : interp V (cons mn (cons M (cons a (cons Aset ρ))))
        (Term.bvar 3) = Aset := by simp [interp_bvar, cons]
    refine WellDenoted_pi_of (Aa := .bvar 3) trivial
      (by rw [hdom]; exact IsTy_of_mem_univ hA)
      (fun bb hbb => h6 Aset a M mn bb hA ha hM (by rwa [hdom] at hbb))
      (fun _ _ => IsTy_piV)
  have h4 : ∀ Aset a M : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      M ∈ˢ eqRecMotiveSpace V (ψ u1N) Aset a →
      WellDenoted V (cons M (cons a (cons Aset ρ)))
        (.pi (eqRecMinorTy ψ)
          (.pi (.bvar 3) (.pi (eqSpine ψ 4 3 0)
            (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))) := by
    intro Aset a M hA ha hM
    obtain ⟨-, hmok, -⟩ := eqRecMinorTy_data ρ hA ha hM
    refine WellDenoted_pi_of hmok.1 hmok.2 (fun mn _ => h5 Aset a M mn hA ha hM)
      (fun _ _ => IsTy_piV)
  have h3 : ∀ Aset a : V, Aset ∈ˢ (univ (ψ uN) : V) → a ∈ˢ Aset →
      WellDenoted V (cons a (cons Aset ρ))
        (.pi (eqRecMotiveTy ψ) (.pi (eqRecMinorTy ψ)
          (.pi (.bvar 3) (.pi (eqSpine ψ 4 3 0)
            (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))) := by
    intro Aset a hA ha
    obtain ⟨hmint, hmok⟩ := eqRecMotiveTy_data ρ hA ha
    refine WellDenoted_pi_of hmok.1 hmok.2
      (fun M hM => h4 Aset a M hA ha (by rwa [hmint] at hM))
      (fun _ _ => IsTy_piV)
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ (ψ uN) : V) →
      WellDenoted V (cons Aset ρ)
        (.pi (.bvar 0) (.pi (eqRecMotiveTy ψ)
          (.pi (eqRecMinorTy ψ)
            (.pi (.bvar 3) (.pi (eqSpine ψ 4 3 0)
              (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))))) := by
    intro Aset hA
    have hdom : interp V (cons Aset ρ) (Term.bvar 0) = Aset := by
      simp [interp_bvar, cons]
    refine WellDenoted_pi_of (Aa := .bvar 0) trivial
      (by rw [hdom]; exact IsTy_of_mem_univ hA)
      (fun a ha => h3 Aset a hA (by rwa [hdom] at ha))
      (fun _ _ => IsTy_piV)
  rw [eqRecTy]
  exact ⟨WellDenoted_pi_of (Aa := .sort (ψ uN)) trivial (IsTy_univ _)
    (fun Aset hA => h2 Aset (by rwa [interp_sort] at hA))
    (fun _ _ => IsTy_piV), IsTy_piV⟩

/-- **`Eq.rec`, installed at the P tier.** -/
theorem extendEqRec (mp : EnvModelM V μ env)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, mp.base2.acval eqName ψ = eqValT ψ)
    (hRv : ∀ ψ : Name → Nat,
      mp.base2.acval eqReflName ψ = eqReflValT ψ)
    (hfresh : env.find? eqRecA.name = none)
    (hwf : EnvWF ⟨eqRecA :: env.consts, env.tables⟩) {ex : List Name} :
    ∃ mp' : EnvModelM V μ ⟨eqRecA :: env.consts, env.tables⟩,
      mp'.base2.acval
        = acvalWith mp.base2.acval eqRecA.name eqRecValT ∧
      (LfpCover mp ex → LfpCover mp' ex) := by
  have hty := fun ψ =>
    denote_eqRecA_type (m := mp.base2) (A := eqRecValT) ψ hE hR hEv hRv
  refine coverA_cons hfresh (fun _ h => h) (fun _ _ h => nomatch h) <|
    declStep_preserves_of_basis_rec_cons mp (A := eqRecValT) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf
      (fun ψ => by exact eqRecValT_closed ψ)
      rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT eqRecA.name ψ
          = none from rfl] at hp
        exact nomatch hp)
      (fun _ _ _ _ heq r hr => by
        injection heq with _ _ _ h4
        rw [← h4] at hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨⟨_, _, _, hR⟩, fun _ => recRuleKOf_of hR rfl hE rfl,
            fun hb => Bool.noConfusion hb⟩
        · exact nomatch hr'))
    (fun ψ₁ ψ₂ hp => eqRecValT_congr
      (hp uN (by
        show uN ∈ [u1N, uN]
        exact List.mem_cons_of_mem _ List.mem_cons_self))
      (hp u1N (by show u1N ∈ [u1N, uN]; exact List.mem_cons_self)))
    (fun ψ ρ => eqRecRaTower_eq ψ ▸ (eqRecRaTower_data ψ ρ).1)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact eqRecTy_wellDenoted ψ ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [← eqRecRaTower_eq ψ]
    exact (eqRecRaTower_data ψ ρ).2
  · intro m₂ hac φ
    refine recRules_cons_rec mp hfresh eqRecA_eq m₂ hac φ ?_
    intro rl hrl
    rcases List.mem_cons.mp hrl with rfl | hr'
    · exact eqRecLaw (m := mp.base2) m₂ hE hR hEv hRv hac φ
    · exact nomatch hr'

/-- **The `Eq` block, installed at the P tier.**  `BasisStepPB`'s
`eqK` branch — the block whose chain reads its own earlier leaves, and
so the one that consumes the install's exposed `acval`. -/
theorem declBasisPB_eqK {env₁ : Env} (mp : EnvModelM V μ env)
    (h : ConLeche.Semantics.BasisInstallRun env
      ConLeche.BasisKind.eqK.declsA env₁) :
    CoverStep mp env₁ := by
  rw [show ConLeche.BasisKind.eqK.declsA = [eqA, eqReflA, eqRecA]
    from rfl] at h
  obtain ⟨h1, h2, h3, hnil⟩ := h
  subst hnil
  have hf1 : env.find? eqName = none := Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨eqA :: env.consts, env.tables⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
  obtain ⟨mp1, hac1, hc1⟩ := extendEq mp hf1 hwf1
  have hEv1 : ∀ ψ : Name → Nat, mp1.base2.acval eqName ψ
      = eqValT ψ := by
    intro ψ
    rw [hac1, show eqName = eqA.name from rfl, acvalWith_self]
  have hE1 : (⟨eqA :: env.consts, env.tables⟩ : Env).find? eqName = some eqA := by
    rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl
  have hf2 : (⟨eqA :: env.consts, env.tables⟩ : Env).find? eqReflA.name = none :=
    Option.isNone_iff_eq_none.mp h2
  have hwf2 : EnvWF ⟨eqReflA :: eqA :: env.consts, env.tables⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ eqReflA.toConstantVal.type = true
    have hf : (⟨eqReflA :: eqA :: env.consts, env.tables⟩ : Env).find? eqName
        = some eqA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hE1
    rw [show eqReflA.toConstantVal.type
        = Expr.forallE (.sort (.param uN))
            (Expr.forallE (.bvar 0)
              (.app (.app (.app (.const eqName [.param uN]) (.bvar 1))
                (.bvar 0)) (.bvar 0))) from rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨mp2, hac2, hc2⟩ := extendEqRefl mp1 hE1 hEv1 hf2 hwf2
  have hE2 : (⟨eqReflA :: eqA :: env.consts, env.tables⟩ : Env).find? eqName
      = some eqA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hE1
  have hR2 : (⟨eqReflA :: eqA :: env.consts, env.tables⟩ : Env).find? eqReflName
      = some eqReflA := by
    rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl
  have hEv2 : ∀ ψ : Name → Nat, mp2.base2.acval eqName ψ
      = eqValT ψ := by
    intro ψ
    rw [hac2, acvalWith_ne (by decide)]
    exact hEv1 ψ
  have hRv2 : ∀ ψ : Name → Nat, mp2.base2.acval eqReflName ψ
      = eqReflValT ψ := by
    intro ψ
    rw [hac2, show eqReflName = eqReflA.name from rfl, acvalWith_self]
  -- the pinned block's lfp clause, recorded at its constructor's cons
  -- (the hand clause `eqLfp`)
  let mp2' := mp2.addLfp (eqLfp eqName eqReflName fun ψ => ψ uN)
    (eqLfp_clause
      (fun ψ ρ A a b hA ha hb => by
        rw [hEv2]; exact eqValT_app₃ ψ ρ A a b hA ha hb)
      (fun ψ ρ => by rw [hRv2]; exact eqReflValT_interp ψ ρ))
    (eqLfp_stored ⟨_, _, hE2⟩ ⟨_, _, _, hR2⟩)
    (eqLfp_reads hE2 fun ψ => denote_eqA_type ψ)
    ⟨rfl, fun c hc j hj => by
      obtain rfl : c = 0 := Nat.lt_one_iff.mp hc
      obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
      refine ⟨eqReflA.toConstantVal, 2, 0, hR2, rfl,
        fun mm hmm => ⟨eqA.toConstantVal, _, by
          obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
          exact hE2, rfl⟩,
        -- `Eq.refl`'s parameter binders read as `Eq`'s parameters
        (fun ψ dsC bodyC hrd hle ρ hsat => by
          match dsC, hle with
          | d0 :: d1 :: rest, _ =>
            rw [show eqReflA.toConstantVal.type
                = Expr.forallE (.sort (.param uN))
                    (Expr.forallE (.bvar 0)
                      (.app (.app (.app (.const eqName [.param uN]) (.bvar 1))
                        (.bvar 0)) (.bvar 0))) from rfl] at hrd
            obtain ⟨ta, ba, hta, hba, he⟩ := denote_forallE_inv hrd
            obtain ⟨tb, bb, htb, -, he'⟩ := denote_forallE_inv hba
            simp only [mkPisAV] at he
            injection he with h0 h1
            rw [← h1] at he'
            injection he' with h2 _
            rw [denote_sort] at hta
            simp only [ConLeche.Expr.instantiate1, ite_true] at htb
            rw [denote_fvar] at htb
            obtain rfl := Option.some.inj hta
            obtain rfl := Option.some.inj htb
            simp only [List.take_succ_cons, List.take_zero, h0, h2]
            exact hsat),
        .app (.fvar 2 (.sort .zero)) (.fvar 1 (.sort .zero)),
        (by decide : ConLeche.nestCanonCrest [eqName] [.param uN] 2 eqReflA.toConstantVal.type
          = some (.app (.fvar 2 (.sort .zero)) (.fvar 1 (.sort .zero)))),
        (by decide : Expr.nestOcc [eqName] 0 0 (.app (.fvar 2 (.sort .zero)) (.fvar 1 (.sort .zero)))
          = false),
        fun ψ => ⟨rfl, rfl, [], [.pi (.bvar 1) (.sort 0)], ?_, rfl, rfl,
          fun mm hmm => by
            obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
            refine ⟨eqA.toConstantVal, _, .forallE (.fvar 0 (.sort .zero)) (.sort .zero), hE2, rfl, ?_⟩
            simp [denote_forallE, denote_sort, denote_fvar, Expr.instantiate1, Level.eval],
          trivial⟩⟩
      simp [denote_app, denote_fvar, mkPisAV, eqLfp]⟩
    (eqLfp_caps hE2
      (fun ψ => by
        show ConLeche.PropWhen.holds ψ (ConLeche.PropWhen.ifAllZero []) = true
        rw [ConLeche.PropWhen.holds_ifAllZero]; rfl)
      ⟨_, _, _, hR2, _, [.bvar 0], rfl⟩)
  have hf3 : (⟨eqReflA :: eqA :: env.consts, env.tables⟩ : Env).find?
      eqRecA.name = none := Option.isNone_iff_eq_none.mp h3
  have hwf3 : EnvWF ⟨eqRecA :: eqReflA :: eqA :: env.consts, env.tables⟩ := by
    have hfE : (⟨eqRecA :: eqReflA :: eqA :: env.consts, env.tables⟩ : Env).find?
        eqName = some eqA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hE2
    have hfR : (⟨eqRecA :: eqReflA :: eqA :: env.consts, env.tables⟩ : Env).find?
        eqReflName = some eqReflA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hR2
    refine EnvWF.cons hwf2 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), ?_,
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
                      (.sort (.param u1N))))
                  (Expr.forallE
                    (.app (.app (.bvar 0) (.bvar 1))
                      (.app (.app (.const eqReflName [.param uN])
                        (.bvar 2)) (.bvar 1)))
                    (Expr.forallE (.bvar 3)
                      (Expr.forallE
                        (.app (.app (.app (.const eqName [.param uN])
                          (.bvar 4)) (.bvar 3)) (.bvar 0))
                        (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))))) from rfl]
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
  obtain ⟨mp3, hac3, hc3⟩ := extendEqRec mp2' hE2 hR2 hEv2 hRv2 hf3 hwf3 (ex := [])
  -- coverage: `Eq`'s former opened the exemption list, its record
  -- closes it
  exact ⟨mp3, (Agrees.cons hf1 hac1).trans ((Agrees.cons hf2 hac2).trans
    ((Agrees.of_acval (mp := mp2) (mp' := mp2') rfl).trans (Agrees.cons hf3 hac3))),
    fun h0 => hc3 ((hc2 (hc1 h0)).addLfp_to _ _ _ _ _ _ (nodup_one _) rfl
    (lfpAll_one (n := eqName) (c := eqA) rfl rfl hE2
      (fun _ _ h => by injection h with _ h; subst h; rfl))
    (lfpOwn_one (T := eqName) (cs := [(eqReflA.toConstantVal, 2, 0)]) rfl rfl hE2
      (by
        show List.filterMap (ctorLook (ConLeche.Env.find? ⟨eqReflA :: eqA :: env.consts, env.tables⟩) eqName)
          [eqReflA.name] = _
        rfl) rfl
      ⟨2, [(eqReflA.toConstantVal, 0)], rfl, rfl, fun j hj => by
        obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
        exact hR2⟩
      (fun _ h => by simp [nestPick] at h) (by decide)
      (fun nP' L h j hj => by
        simp only [nestPick, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain rfl : j = 0 := by simp at hj; omega
        exact ⟨_, [.bvar 1, .bvar 0, .bvar 0], rfl, fun _ => rfl⟩))
    (filter_not_mem_self _))⟩

end Eq

end ConLeche.Model
