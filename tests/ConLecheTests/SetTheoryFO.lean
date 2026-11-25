module

public import ConLeche.SetTheory.Basic
public import ConLeche.IsModel
public import ConLecheTests.OldSetTheory

@[expose] public section

/-!
# Reverse bridge, `Expr.eval` equation pins, and first-order smoke tests

1. Imports the old second-order class, `ConLecheOld.SetTheory`
   (`tests/ConLecheTests/OldSetTheory.lean`): `ConLeche/SetTheory/Core.lean` as it was
   before the first-order rewrite, identical but for its namespace
   (`tests/old-set-theory.sh`).
2. Proves `setTheoryOfSecondOrder : ConLecheOld.SetTheory V → SetTheory V`: every model of
   the old class is a model of the current one
   (including `isGrothendieck_of_isTGUniverse` via Cantor's diagonal
   `covered_mem` and the 2-cycle `sUnion_mem` proof), pinning its axiom
   footprint to `[propext, Classical.choice, Quot.sound]`.
3. Pins `Expr.eval` `lam` / `forallE` / β-reduction / truth-value laws
   and `#print axioms` after the first-order rewrite of `IsModel`.
4. Smoke-tests `Formula.eval`, `DefFun`/`fo_def`, `natrec`, `natzero`,
   and `natsucc`.
-/

namespace ConLecheTests.SetTheoryFO

open ConLeche ConLeche.SetTheory

universe u

section ReverseBridge

def kpairSO {V : Type u} (S : ConLecheOld.SetTheory V) (a b : V) : V :=
  S.upair (S.upair a a) (S.upair a b)

theorem isUpair_upairSO {V : Type u} (S : ConLecheOld.SetTheory V) (a b : V) :
    IsUpair S.Mem (S.upair a b) a b :=
  fun _ => S.mem_upair

theorem isKPair_kpairSO {V : Type u} (S : ConLecheOld.SetTheory V) (a b : V) :
    IsKPair S.Mem (kpairSO S a b) a b :=
  ⟨S.upair a a, S.upair a b, isUpair_upairSO S a a, isUpair_upairSO S a b,
    isUpair_upairSO S (S.upair a a) (S.upair a b)⟩

theorem kpairSO_inj {V : Type u} (S : ConLecheOld.SetTheory V) {a₁ b₁ a₂ b₂ : V}
    (h : kpairSO S a₁ b₁ = kpairSO S a₂ b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  unfold kpairSO at h
  have upair_inj : ∀ {x y z : V}, S.upair x y = S.upair z z → x = z ∧ y = z := fun {x y z} heq => by
    have hx : S.Mem x (S.upair z z) := heq ▸ S.mem_upair.mpr (Or.inl rfl)
    have hy : S.Mem y (S.upair z z) := heq ▸ S.mem_upair.mpr (Or.inr rfl)
    exact ⟨(S.mem_upair.mp hx).elim id id, (S.mem_upair.mp hy).elim id id⟩
  have h1 : S.Mem (S.upair a₁ a₁) (S.upair (S.upair a₂ a₂) (S.upair a₂ b₂)) :=
    h ▸ S.mem_upair.mpr (Or.inl rfl)
  have h2 : S.Mem (S.upair a₁ b₁) (S.upair (S.upair a₂ a₂) (S.upair a₂ b₂)) :=
    h ▸ S.mem_upair.mpr (Or.inr rfl)
  have ha : a₁ = a₂ := by
    rcases S.mem_upair.mp h1 with hsing | hpair
    · exact (upair_inj hsing).1
    · exact (upair_inj hpair.symm).1.symm
  subst ha
  refine ⟨rfl, ?_⟩
  rcases S.mem_upair.mp h2 with hsing | hpair
  · have hb1 : b₁ = a₁ := (upair_inj hsing).2
    have h3 : S.Mem (S.upair a₁ b₂) (S.upair (S.upair a₁ a₁) (S.upair a₁ b₁)) :=
      h.symm ▸ S.mem_upair.mpr (Or.inr rfl)
    rcases S.mem_upair.mp h3 with hsing' | hpair'
    · exact hb1.trans (upair_inj hsing').2.symm
    · have hb2 : b₂ = a₁ := (upair_inj (hpair'.trans hsing)).2
      exact hb1.trans hb2.symm
  · by_cases hba : b₁ = a₁
    · subst hba
      exact (upair_inj hpair.symm).2.symm
    · have hb2 : S.Mem b₁ (S.upair a₁ b₂) := hpair ▸ S.mem_upair.mpr (Or.inr rfl)
      exact (S.mem_upair.mp hb2).elim (fun h => absurd h hba) id

theorem no_two_cycle_SO {V : Type u} (S : ConLecheOld.SetTheory V) {x y : V}
    (hxy : S.Mem x y) (hyx : S.Mem y x) : False := by
  obtain ⟨m, hm, hmin⟩ := S.regularity (S.upair x y) ⟨x, S.mem_upair.mpr (Or.inl rfl)⟩
  rcases S.mem_upair.mp hm with rfl | rfl
  · exact hmin ⟨y, hyx, S.mem_upair.mpr (Or.inr rfl)⟩
  · exact hmin ⟨x, hxy, S.mem_upair.mpr (Or.inl rfl)⟩

theorem tg_power_mem_SO {V : Type u} (S : ConLecheOld.SetTheory V) {u y : V}
    (hu : ConLecheOld.IsTGUniverse S.Mem u) (hy : S.Mem y u) : S.Mem (S.power y) u := by
  obtain ⟨p, hp, hsub⟩ := hu.2.2.1 y hy
  exact hu.2.1 p (S.power y) hp fun z hz => hsub z (S.mem_power.mp hz)

open Classical in
theorem tg_covered_mem_SO {V : Type u} (S : ConLecheOld.SetTheory V) {u I Sset : V}
    {F : V → V} (hu : ConLecheOld.IsTGUniverse S.Mem u) (hI : S.Mem I u)
    (hS : ∀ w, S.Mem w Sset → S.Mem w u)
    (hcov : ∀ b, S.Mem b Sset → ∃ x, S.Mem x I ∧ F x = b) :
    S.Mem Sset u := by
  rcases hu.2.2.2 Sset hS with ⟨f, -, -, hsurj⟩ | hmem
  · exfalso
    by_cases hex : ∃ w₀, S.Mem w₀ I ∧ ¬ S.Mem w₀ (f (F w₀))
    · obtain ⟨w₀, hw₀I, hw₀P⟩ := hex
      let D := S.image (fun x => if ¬ S.Mem x (f (F x)) then x else w₀) I
      have hD_sub : ∀ w, S.Mem w D → S.Mem w I := fun w hw => by
        obtain ⟨x, hx, rfl⟩ := S.mem_image.mp hw
        split <;> assumption
      have hDu : S.Mem D u := hu.2.1 I D hI hD_sub
      obtain ⟨b, hbS, hfb⟩ := hsurj D hDu
      obtain ⟨j, hjI, hFj⟩ := hcov b hbS
      have hGj : f (F j) = D := by rw [hFj, hfb]
      have hmemD : ∀ x, S.Mem x D ↔ S.Mem x I ∧ ¬ S.Mem x (f (F x)) := fun x => by
        dsimp only [D]; rw [S.mem_image]
        constructor
        · rintro ⟨z, hzI, rfl⟩
          by_cases hz : ¬ S.Mem z (f (F z))
          · rw [ite_eq_left hz]; exact ⟨hzI, hz⟩
          · rw [ite_eq_right hz]; exact ⟨hw₀I, hw₀P⟩
        · rintro ⟨hxI, hxP⟩
          exact ⟨x, hxI, (ite_eq_left hxP).symm⟩
      by_cases hj : S.Mem j D
      · exact (hmemD j).mp hj |>.2 (hGj ▸ hj)
      · exact hj ((hmemD j).mpr ⟨hjI, fun h => hj (hGj ▸ h)⟩)
    · obtain ⟨e, heu, hemin⟩ := S.regularity u ⟨I, hI⟩
      have he_empty : ∀ z, ¬ S.Mem z e := fun z hze =>
        hemin ⟨z, hze, hu.1 e z heu hze⟩
      obtain ⟨b, hbS, hfb⟩ := hsurj e heu
      obtain ⟨j, hjI, hFj⟩ := hcov b hbS
      have hjf : S.Mem j (f (F j)) := Classical.byContradiction fun h => hex ⟨j, hjI, h⟩
      rw [hFj, hfb] at hjf
      exact he_empty j hjf
  · exact hmem

theorem tg_image_mem_SO {V : Type u} (S : ConLecheOld.SetTheory V) {u A : V} {F : V → V}
    (hu : ConLecheOld.IsTGUniverse S.Mem u) (hA : S.Mem A u) (hF : ∀ x, S.Mem x A → S.Mem (F x) u) :
    S.Mem (S.image F A) u :=
  tg_covered_mem_SO S hu hA
    (fun _ hz => let ⟨w, hw, eq⟩ := S.mem_image.mp hz; eq ▸ hF w hw)
    (fun _ hb => let ⟨w, hw, eq⟩ := S.mem_image.mp hb; ⟨w, hw, eq.symm⟩)

open Classical in
theorem tg_upair_mem_SO {V : Type u} (S : ConLecheOld.SetTheory V) {u a b : V}
    (hu : ConLecheOld.IsTGUniverse S.Mem u) (ha : S.Mem a u) (hb : S.Mem b u) :
    S.Mem (S.upair a b) u := by
  obtain ⟨e, heu, hemin⟩ := S.regularity u ⟨a, ha⟩
  have he_empty : ∀ z, ¬ S.Mem z e := fun z hze =>
    hemin ⟨z, hze, hu.1 e z heu hze⟩
  have hp1 : S.Mem (S.power e) u := tg_power_mem_SO S hu heu
  have hp2 : S.Mem (S.power (S.power e)) u := tg_power_mem_SO S hu hp1
  refine tg_covered_mem_SO S (F := fun x => if x = e then a else b) hu hp2 ?_ ?_
  · intro z hz
    rcases S.mem_upair.mp hz with rfl | rfl <;> assumption
  · intro z hz
    rcases S.mem_upair.mp hz with rfl | rfl
    · refine ⟨e, S.mem_power.mpr (fun w hw => absurd hw (he_empty w)), ?_⟩
      exact ite_eq_left rfl
    · have hne : S.power e ≠ e := fun heq => by
        have hm : S.Mem e (S.power e) := S.mem_power.mpr fun _ hw => hw
        rw [heq] at hm
        exact he_empty e hm
      refine ⟨S.power e, S.mem_power.mpr (fun _ hw => hw), ?_⟩
      exact ite_eq_right hne

theorem tg_sUnion_mem_SO {V : Type u} (S : ConLecheOld.SetTheory V) {u s : V}
    (hu : ConLecheOld.IsTGUniverse S.Mem u) (hs : S.Mem s u) : S.Mem (S.sUnion s) u := by
  have hsub : ∀ z, S.Mem z (S.sUnion s) → S.Mem z u := fun z hz => by
    obtain ⟨y, hy, hzy⟩ := S.mem_sUnion.mp hz
    exact hu.1 y z (hu.1 s y hs hy) hzy
  rcases hu.2.2.2 (S.sUnion s) hsub with ⟨f, hinto, -, hsurj⟩ | hmem
  · exfalso
    have himg : ∀ w, S.Mem w s → S.Mem (S.image f w) u := fun w hw =>
      tg_image_mem_SO S hu (hu.1 s w hs hw) fun x hx =>
        hinto x (S.mem_sUnion.mpr ⟨w, hw, hx⟩)
    have hS : S.Mem (S.image (fun w => S.image f w) s) u :=
      tg_image_mem_SO S hu hs himg
    obtain ⟨x, hx, hfx⟩ := hsurj _ hS
    obtain ⟨w, hw, hxw⟩ := S.mem_sUnion.mp hx
    have h1 : S.Mem (S.image (fun w => S.image f w) s) (S.image f w) :=
      hfx ▸ S.mem_image.mpr ⟨x, hxw, rfl⟩
    have h2 : S.Mem (S.image f w) (S.image (fun w => S.image f w) s) :=
      S.mem_image.mpr ⟨w, hw, rfl⟩
    exact no_two_cycle_SO S h1 h2
  · exact hmem

open Classical in
theorem isGrothendieck_of_isTGUniverse {V : Type u} (S : ConLecheOld.SetTheory V)
    {u : V} (hu : ConLecheOld.IsTGUniverse S.Mem u) : IsGrothendieck S.Mem u := by
  refine ⟨hu.1, fun a b ha hb => ?_, fun y hy => ?_, fun I g hIu hg => ?_⟩
  · exact ⟨S.upair a b, tg_upair_mem_SO S hu ha hb, isUpair_upairSO S a b⟩
  · exact ⟨S.power y, tg_power_mem_SO S hu hy, fun z => S.mem_power⟩
  · have hval : ∀ i, S.Mem i I →
        ∃ y, S.Mem y u ∧ ∃ p, S.Mem p g ∧ IsKPair S.Mem p i y := fun i hi => by
      obtain ⟨y, hy, _⟩ := hg.2 i hi
      exact ⟨y, hy⟩
    let F : V → V := fun i =>
      if hi : S.Mem i I then Classical.choose (hval i hi) else I
    have hF_spec : ∀ i (hi : S.Mem i I),
        S.Mem (F i) u ∧ ∃ p, S.Mem p g ∧ IsKPair S.Mem p i (F i) := fun i hi => by
      dsimp only [F]; rw [dite_eq_left hi]
      exact Classical.choose_spec (hval i hi)
    let Y : V := S.image F I
    have hYu : S.Mem Y u := tg_image_mem_SO S hu hIu fun i hi => (hF_spec i hi).1
    refine ⟨S.sUnion Y, tg_sUnion_mem_SO S hu hYu, fun z => ?_⟩
    rw [S.mem_sUnion]
    constructor
    · rintro ⟨y, hyY, hzy⟩
      obtain ⟨i, hi, rfl⟩ := S.mem_image.mp hyY
      obtain ⟨hyu, p, hpg, hkp⟩ := hF_spec i hi
      exact ⟨i, F i, p, hi, hyu, hpg, hkp, hzy⟩
    · rintro ⟨i, y, p, hi, hyu, hpg, hkp, hzy⟩
      have hy_eq : y = F i := (hg.2 i hi).unique ⟨hyu, p, hpg, hkp⟩ (hF_spec i hi)
      subst hy_eq
      exact ⟨F i, S.mem_image.mpr ⟨i, hi, rfl⟩, hzy⟩

open Classical in
/-- **Every model of the old second-order class is a model of the first-order one**: an
instance of `ConLecheOld.SetTheory`, the class of `ConLeche/SetTheory/Core.lean` before the
first-order rewrite (`tests/ConLecheTests/OldSetTheory.lean`), induces a first-order
`ConLeche.SetTheory`. -/
@[instance_reducible]
noncomputable def setTheoryOfSecondOrder {V : Type u} (S : ConLecheOld.SetTheory V) :
    ConLeche.SetTheory V where
  Mem := S.Mem
  ext := S.ext
  upair := S.upair
  mem_upair := S.mem_upair
  sUnion := S.sUnion
  mem_sUnion := S.mem_sUnion
  power := S.power
  mem_power := S.mem_power
  regularity := S.regularity
  replacement {p} φ params a h := by
    let f : V → V := fun x =>
      if hx : S.Mem x a then Classical.choose (h x hx).exists else a
    refine ⟨S.image f a, fun z => ?_⟩
    rw [S.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      dsimp only [f]; rw [dite_eq_left hx]
      exact Classical.choose_spec (h x hx).exists
    · rintro ⟨x, hx, hφ⟩
      refine ⟨x, hx, ?_⟩
      dsimp only [f]; rw [dite_eq_left hx]
      exact (h x hx).unique hφ (Classical.choose_spec (h x hx).exists)
  choice x h := by
    let g : V → V := fun a =>
      if ha : S.Mem a x then kpairSO S a (Classical.choose (h a ha)) else a
    refine ⟨S.image g x, ?_, ?_⟩
    · intro p hp
      obtain ⟨a, ha, rfl⟩ := S.mem_image.mp hp
      dsimp only [g]; rw [dite_eq_left ha]
      exact ⟨a, Classical.choose (h a ha), ha, Classical.choose_spec (h a ha),
        isKPair_kpairSO S a _⟩
    · intro a ha
      refine ⟨Classical.choose (h a ha), ⟨Classical.choose_spec (h a ha), g a,
        S.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩, ?_⟩
      · dsimp only [g]; rw [dite_eq_left ha]
        exact isKPair_kpairSO S a _
      · rintro y ⟨_, p, hp, hkp⟩
        obtain ⟨a', ha', rfl⟩ := S.mem_image.mp hp
        dsimp only [g] at hkp; rw [dite_eq_left ha'] at hkp
        have h1 := isKPair_kpairSO S a' (Classical.choose (h a' ha'))
        have kpair_eq_kpairSO : ∀ {p x₁ y₁ : V},
            IsKPair S.Mem p x₁ y₁ → p = kpairSO S x₁ y₁ := by
          intro p x₁ y₁ ⟨s, t, hs, ht, hp⟩
          have hs_eq : s = S.upair x₁ x₁ := S.ext fun z => (hs z).trans S.mem_upair.symm
          have ht_eq : t = S.upair x₁ y₁ := S.ext fun z => (ht z).trans S.mem_upair.symm
          subst hs_eq; subst ht_eq
          exact S.ext fun z => (hp z).trans S.mem_upair.symm
        have heq : kpairSO S a' (Classical.choose (h a' ha')) = kpairSO S a y :=
          (kpair_eq_kpairSO h1).symm.trans (kpair_eq_kpairSO hkp)
        obtain ⟨rfl, hy⟩ := kpairSO_inj S heq
        exact hy.symm
  univChain := S.univChain
  univChain_mem := S.univChain_mem
  univChain_grothendieck n := isGrothendieck_of_isTGUniverse S (S.univChain_tg n)

/--
info: 'ConLecheTests.SetTheoryFO.setTheoryOfSecondOrder' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms setTheoryOfSecondOrder

end ReverseBridge

section EvalPins

open ConLeche.SetModel

variable {V : Type u} [SetTheory V]

/-- Equation pin for `Expr.eval` on `.lam`. -/
theorem eval_lam_pin (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (ty body : Expr) :
    Expr.eval model φ ρ (.lam ty body) =
      lamV (Expr.eval model φ ρ ty) (fun x => Expr.eval model φ (push x ρ) body)
        (eval_hasGraph_push model φ ρ (Expr.eval model φ ρ ty) body) :=
  eval_lam model φ ρ ty body

/-- Equation pin for `Expr.eval` on `.forallE`. -/
theorem eval_forallE_pin (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (ty body : Expr) :
    Expr.eval model φ ρ (.forallE ty body) =
      piV (Expr.eval model φ ρ ty) (fun x => Expr.eval model φ (push x ρ) body)
        (eval_hasSigmaPairs_push model φ ρ (Expr.eval model φ ρ ty) body) :=
  eval_forallE model φ ρ ty body

/-- β-reduction equation pin for `Expr.eval` on `.app (.lam ty body) arg`. -/
theorem eval_beta_pin (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (ty body arg : Expr)
    (harg : Expr.eval model φ ρ arg ∈ˢ Expr.eval model φ ρ ty) :
    Expr.eval model φ ρ (.app (.lam ty body) arg) =
      Expr.eval model φ (push (Expr.eval model φ ρ arg) ρ) body := by
  rw [eval_app, eval_lam, app_lamV harg]

/-- Truth-value Π pin: `∀ (x : Prop), x` evaluates to `truthVal` over `univ 0`
inside `univ 0`. -/
theorem eval_truthVal_pi_pin (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) :
    Expr.eval model φ ρ (.forallE (.sort .zero) (.bvar 0)) =
      truthVal (∀ x, x ∈ˢ (univ 0 : V) → ∃ y, y ∈ˢ x) := by
  rw [eval_forallE, eval_sort, Level.eval]
  unfold piV
  have hprop : propN (univ 0 : V) (fun x => Expr.eval model φ (push x ρ) (.bvar 0)) = 0 := by
    refine propN_eq_zero.mpr fun x hx => ?_
    rw [eval_bvar]
    exact (univ_zero (V := V)) ▸ hx
  rw [hprop, piR_zero]
  exact truthVal_congr
    ⟨fun h x hx => let ⟨y, hy⟩ := h x hx; ⟨y, by rw [eval_bvar] at hy; exact hy⟩,
     fun h x hx => let ⟨y, hy⟩ := h x hx; ⟨y, by rw [eval_bvar]; exact hy⟩⟩

/--
info: 'ConLecheTests.SetTheoryFO.eval_lam_pin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms eval_lam_pin

/--
info: 'ConLecheTests.SetTheoryFO.eval_forallE_pin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms eval_forallE_pin

/--
info: 'ConLecheTests.SetTheoryFO.eval_beta_pin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms eval_beta_pin

/--
info: 'ConLecheTests.SetTheoryFO.eval_truthVal_pi_pin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms eval_truthVal_pi_pin

end EvalPins

section SmokeTests

variable {V : Type u} [SetTheory V]

/-- `Formula.eval` smoke test: non-emptiness sentence `∃ y, y ∈ x`. -/
theorem formula_nonempty_iff (x : V) :
    (Formula.exists_ (.mem 0 1)).eval Mem (fcons x Fin.elim0) ↔ ∃ y : V, y ∈ˢ x := by
  simp only [Formula.eval_exists, Formula.eval_mem, fcons_zero]
  exact Iff.rfl

/-- `DefFun` / `fo_def` smoke test for pairing. -/
theorem defFun_upair_smoke : DefFun 2 fun v : Fin 2 → V => upair (v 0) (v 1) := by
  fo_def

/-- `DefFun` / `fo_def` smoke test combining `natrec`, `natzero`, and `natsucc`. -/
theorem defFun_natrec_smoke :
    DefFun 1 fun v : Fin 1 → V => natrec natzero (v 0) (natsucc natzero) := by
  fo_def [DefFun.natrec_apply, DefFun.natzero, DefFun.natsucc_apply]

theorem natrec_smoke_eq (s : V) :
    natrec (natzero : V) s (natsucc natzero) = app (app s natzero) natzero := by
  unfold natsucc natzero
  rw [natrec_vsucc empty s empty_mem_omega, natrec_empty]

end SmokeTests

end ConLecheTests.SetTheoryFO
