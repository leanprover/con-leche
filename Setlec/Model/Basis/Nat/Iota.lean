import Setlec.Model.BasisInstall

/-!
# `Nat.rec` iota-rule semantics (both rules)
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-! ## The `Nat.rec` rules -/

/-- The (annotated) rhs of `Nat.rec`'s zero rule. -/
def natRecZeroRhsA : Expr := ((ConstantInfo.recRules natRecA).getD 0 default).rhs

/-- The (annotated) rhs of `Nat.rec`'s successor rule. -/
def natRecSuccRhsA : Expr := ((ConstantInfo.recRules natRecA).getD 1 default).rhs

/-- Raw-shaped evaluation of the zero rule's minor-premise λ tag. -/
def nrZ (u : Nat) : Nat := if u = 0 then 0 else Nat.max (en11UU u) u

/-- Raw-shaped evaluation of the zero rule's motive λ tag. -/
def nrM (u : Nat) : Nat := if nrZ u = 0 then 0 else Nat.max u (nrZ u)

theorem nrZ_eq (u : Nat) : nrZ u = if u = 0 then 0 else Nat.max 1 u := by
  unfold nrZ
  rw [en11UU_eq]
  by_cases h : u = 0
  · simp [h]
  · simp only [if_neg h]
    exact Nat.le_antisymm
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
      (Nat.le_max_left _ _)

theorem nrM_eq (u : Nat) : nrM u = if u = 0 then 0 else Nat.max 1 u := by
  unfold nrM
  rw [nrZ_eq]
  by_cases h : u = 0
  · simp [h]
  · simp only [if_neg h]
    rw [if_neg (max_ne_zero_l (by decide) : Nat.max 1 u ≠ 0)]
    exact max_absorb_r' 1 u

/-- Interpretation of the `Nat.rec` zero rule rhs. -/
theorem interp_natRecZero_rhs {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ') :
    interpClosed V cval env ψ natRecZeroRhsA =
      some (SetTheory.lam (nrM (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (nrZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _s => z) := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  have hfindZ' : env.find? ((Name.anonymous.str "Nat").str "zero") = some natZeroA :=
    hfindZ
  have hvalZ' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "zero") ψ' = natzero := hvalZ
  have hfindSc' : env.find? ((Name.anonymous.str "Nat").str "succ") = some natSuccA :=
    hfindSc
  have hvalSc' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "succ") ψ' = natSuccVal V ψ' := hvalSc
  simp only [interpClosed, natRecZeroRhsA, natRecA, ConstantInfo.recRules,
    List.getD, List.getElem?_cons_zero, Option.getD_some,
    interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindN', hvalN', hfindZ', hvalZ', hfindSc', hvalSc', natA, natZeroA,
    natSuccA, List.length_cons, List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, nrM, nrZ, en11UU, enUU,
    ConstantInfo.toConstantVal,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- Interpretation of the `Nat.rec` successor rule rhs. -/
theorem interp_natRecSucc_rhs {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    (hfindR : env.find? (natName.str "rec") = some natRecA)
    (hvalR : ∀ ψ' : Name → Nat, cval (natName.str "rec") ψ' = natRecVal V ψ') :
    interpClosed V cval env ψ natRecSuccRhsA =
      some (SetTheory.lam (enM (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (enZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun s =>
            SetTheory.lam (ψ uN) omega fun n =>
              SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n)) := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  have hfindZ' : env.find? ((Name.anonymous.str "Nat").str "zero") = some natZeroA :=
    hfindZ
  have hvalZ' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "zero") ψ' = natzero := hvalZ
  have hfindSc' : env.find? ((Name.anonymous.str "Nat").str "succ") = some natSuccA :=
    hfindSc
  have hvalSc' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "succ") ψ' = natSuccVal V ψ' := hvalSc
  have hfindR' : env.find? ((Name.anonymous.str "Nat").str "rec") = some natRecA :=
    hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "rec") ψ' = natRecVal V ψ' := hvalR
  simp only [interpClosed, natRecSuccRhsA, natRecA, ConstantInfo.recRules,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some,
    interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindN', hvalN', hfindZ', hvalZ', hfindSc', hvalSc', hfindR', hvalR',
    natA, natZeroA, natSuccA,
    List.length_cons, List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, enM, enZ, en1U, en11UU, enUU,
    hfindN', hvalN', hfindZ', hvalZ', hfindSc', hvalSc', hfindR', hvalR',
    ConstantInfo.toConstantVal,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- The `Nat.rec` value applied through its telescope is set-theoretic
recursion. -/
theorem natRecVal_fold {Mv zv sv nv : V}
    (hM : Mv ∈ˢ pi (ψ uN + 1) omega fun _ => univ (ψ uN))
    (hz : zv ∈ˢ SetTheory.app Mv natzero)
    (hs : sv ∈ˢ pi (ψ uN) omega fun n =>
      pi (ψ uN) (SetTheory.app Mv n) fun _ =>
        SetTheory.app Mv (natsucc n))
    (hn : nv ∈ˢ omega) :
    SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
      (natRecVal V ψ) Mv) zv) sv) nv = natrec zv sv nv := by
  have hMfib : ∀ n, n ∈ˢ omega → SetTheory.app Mv n ∈ˢ univ (ψ uN) :=
    fun n hn' => app_mem hM hn' (fun _ _ => univ_mem_univ (ψ uN))
  have hstep : ∀ k, k ∈ˢ omega → ∀ ih, ih ∈ˢ SetTheory.app Mv k →
      SetTheory.app (SetTheory.app sv k) ih ∈ˢ
        SetTheory.app Mv (natsucc k) := by
    intro k hk ih hih
    have hsfib : ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro n hn'
      have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib n hn')
        (fun _ _ => hMfib (natsucc n) (natsucc_mem hn'))
      by_cases hu : ψ uN = 0
      · simpa [hu] using this
      · simpa [hu, Nat.max_self] using this
    exact app_mem (app_mem hs hk hsfib) hih
      (fun _ _ => hMfib (natsucc k) (natsucc_mem hk))
  by_cases h0 : ψ uN = 0
  · -- Prop collapse: both sides are the proof point
    have hL : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (natRecVal V ψ) Mv) zv) sv) nv = pt := by
      simp only [natRecVal, h0, reduceIte]
      rw [lam_zero, app_pt, app_pt, app_pt, app_pt]
    rw [hL]
    exact (mem_univ_zero (h0 ▸ hMfib nv hn)
      (natrec_mem hz hstep hn)).symm
  · simp only [natRecVal, if_neg h0]
    have hsfib : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro M hM' n hn'
      have hMfib' : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ uN) :=
        fun k hk => app_mem hM' hk (fun _ _ => univ_mem_univ (ψ uN))
      have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib' n hn')
        (fun _ _ => hMfib' (natsucc n) (natsucc_mem hn'))
      rw [if_neg h0,
        show Nat.max (ψ uN) (ψ uN) = ψ uN from Nat.max_self _] at this
      exact this
    have hSsp : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) ∈ˢ univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n))
        (omega_mem_univ (V := V))
        (fun n hn' => hsfib M hM' n hn')
      rw [if_neg h0] at this
      exact this
    have hT4 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun t => SetTheory.app M t)
        (omega_mem_univ (V := V))
        (fun t ht => app_mem hM' ht (fun _ _ => univ_mem_univ (ψ uN)))
      rw [if_neg h0] at this
      exact this
    have hwne : Nat.max 1 (ψ uN) ≠ 0 := max_ne_zero_l (by decide)
    have hT3 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := Nat.max 1 (ψ uN))
        (hSsp M hM') (fun _ _ => hT4 M hM')
      rw [if_neg hwne, show Nat.max (Nat.max 1 (ψ uN)) (Nat.max 1 (ψ uN)) =
        Nat.max 1 (ψ uN) from Nat.max_self _] at this
      exact this
    have hT2 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun _ =>
            pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app M t)
        (app_mem hM' natzero_mem (fun _ _ => univ_mem_univ (ψ uN)))
        (fun _ _ => hT3 M hM')
      rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
      exact this
    have hrecmem : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ z, z ∈ˢ SetTheory.app M natzero →
        ∀ s, s ∈ˢ (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) →
        ∀ t, t ∈ˢ omega → natrec z s t ∈ˢ SetTheory.app M t := by
      intro M hM' z hz' s hs' t ht'
      refine natrec_mem hz' ?_ ht'
      intro k hk ih hih
      exact app_mem (app_mem hs' hk (hsfib M hM')) hih
        (fun _ _ => app_mem hM' (natsucc_mem hk)
          (fun _ _ => univ_mem_univ (ψ uN)))
    have h1 := app_lam (v := Nat.max 1 (ψ uN)) (a := Mv)
      (A := pi (ψ uN + 1) omega fun _ => univ (ψ uN)) hM
      (B := fun M => pi (Nat.max 1 (ψ uN))
        (SetTheory.app M natzero) fun _ =>
        pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app M t)
      (F := fun M => SetTheory.lam (Nat.max 1 (ψ uN))
        (SetTheory.app M natzero) fun z =>
        SetTheory.lam (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun s =>
          SetTheory.lam (ψ uN) omega fun t => natrec z s t)
      (fun M hM' => lam_mem (V := V) fun z hz' =>
        lam_mem (V := V) fun s hs' =>
          lam_mem (V := V) fun t ht' => hrecmem M hM' z hz' s hs' t ht')
      (fun M hM' => hT2 M hM')
    rw [h1]
    have h2 := app_lam (v := Nat.max 1 (ψ uN)) (a := zv)
      (A := SetTheory.app Mv natzero) hz
      (B := fun _ => pi (Nat.max 1 (ψ uN))
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (natsucc n)) fun _ =>
        pi (ψ uN) omega fun t => SetTheory.app Mv t)
      (F := fun z => SetTheory.lam (Nat.max 1 (ψ uN))
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (natsucc n)) fun s =>
          SetTheory.lam (ψ uN) omega fun t => natrec z s t)
      (fun z hz' => lam_mem (V := V) fun s hs' =>
        lam_mem (V := V) fun t ht' => hrecmem Mv hM z hz' s hs' t ht')
      (fun _ _ => hT3 Mv hM)
    rw [h2]
    have h3 := app_lam (v := Nat.max 1 (ψ uN)) (a := sv)
      (A := pi (ψ uN) omega fun n =>
        pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (natsucc n)) hs
      (B := fun _ => pi (ψ uN) omega fun t => SetTheory.app Mv t)
      (F := fun s => SetTheory.lam (ψ uN) omega fun t => natrec zv s t)
      (fun s hs' => lam_mem (V := V) fun t ht' =>
        hrecmem Mv hM zv hz s hs' t ht')
      (fun _ _ => hT4 Mv hM)
    rw [h3]
    exact app_lam (v := ψ uN) (a := nv) (A := omega) hn
      (B := fun t => SetTheory.app Mv t)
      (F := fun t => natrec zv sv t)
      (fun t ht' => hrecmem Mv hM zv hz sv hs t ht')
      (fun t ht' => hMfib t ht')


/-- The fold equation of `Nat.rec`'s zero rule. -/
theorem natZero_iota {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    {Mv zv sv : V}
    (hM : Mv ∈ˢ pi (ψ uN + 1) omega fun _ => univ (ψ uN))
    (hz : zv ∈ˢ SetTheory.app Mv natzero)
    (hs : sv ∈ˢ pi (ψ uN) omega fun n =>
      pi (ψ uN) (SetTheory.app Mv n) fun _ =>
        SetTheory.app Mv (natsucc n)) :
    ∃ R, interpClosed V cval env ψ natRecZeroRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (natRecVal V ψ) Mv) zv) sv) natzero =
      SetTheory.app (SetTheory.app (SetTheory.app R Mv) zv) sv := by
  refine ⟨_, interp_natRecZero_rhs hfindN hvalN hfindZ hvalZ hfindSc hvalSc,
    ?_⟩
  rw [natRecVal_fold hM hz hs natzero_mem, natrec_zero]
  have hMfib : ∀ n, n ∈ˢ omega → SetTheory.app Mv n ∈ˢ univ (ψ uN) :=
    fun n hn' => app_mem hM hn' (fun _ _ => univ_mem_univ (ψ uN))
  by_cases h0 : ψ uN = 0
  · -- Prop collapse: the rhs value is the proof point, and so is `zv`
    have hR : SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.lam (nrM (ψ uN))
          (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
          SetTheory.lam (nrZ (ψ uN)) (SetTheory.app M natzero) fun z =>
            SetTheory.lam (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              fun _s => z) Mv) zv) sv = pt := by
      rw [show nrM (ψ uN) = 0 from by rw [nrM_eq, if_pos h0]]
      rw [lam_zero, app_pt, app_pt, app_pt]
    rw [hR]
    exact mem_univ_zero (h0 ▸ hMfib natzero natzero_mem) hz
  · -- data levels: the rhs value projects out the minor premise
    rw [show nrM (ψ uN) = Nat.max 1 (ψ uN) from by rw [nrM_eq, if_neg h0],
      show nrZ (ψ uN) = Nat.max 1 (ψ uN) from by rw [nrZ_eq, if_neg h0],
      enUU_eq]
    have hSspEq : ∀ M : V,
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) := fun M =>
      pi_congr fun n hn' => by rw [natSuccVal_app hn']
    have hsfib : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro M hM' n hn'
      have hMfib' : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ uN) :=
        fun k hk => app_mem hM' hk (fun _ _ => univ_mem_univ (ψ uN))
      have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib' n hn')
        (fun _ _ => hMfib' (natsucc n) (natsucc_mem hn'))
      rw [if_neg h0,
        show Nat.max (ψ uN) (ψ uN) = ψ uN from Nat.max_self _] at this
      exact this
    have hSsp : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) ∈ˢ univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n))
        (omega_mem_univ (V := V))
        (fun n hn' => hsfib M hM' n hn')
      rw [if_neg h0] at this
      exact this
    have hwne : Nat.max 1 (ψ uN) ≠ 0 := max_ne_zero_l (by decide)
    have hT3 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN)
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          SetTheory.app M natzero) ∈ˢ univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := ψ uN)
        (B := fun _ => SetTheory.app M natzero)
        (hSsp M hM')
        (fun _ _ => app_mem hM' natzero_mem
          (fun _ _ => univ_mem_univ (ψ uN)))
      rw [if_neg h0,
        show Nat.max (Nat.max 1 (ψ uN)) (ψ uN) = Nat.max 1 (ψ uN) from
          Nat.le_antisymm
            (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
            (Nat.le_max_left _ _)] at this
      exact this
    have hT2 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (ψ uN)
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun _ =>
            SetTheory.app M natzero) ∈ˢ univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (ψ uN)
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          SetTheory.app M natzero)
        (app_mem hM' natzero_mem (fun _ _ => univ_mem_univ (ψ uN)))
        (fun _ _ => hT3 M hM')
      rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
      exact this
    have h1 := app_lam (v := Nat.max 1 (ψ uN)) (a := Mv)
      (A := pi (ψ uN + 1) omega fun _ => univ (ψ uN)) hM
      (B := fun M => pi (Nat.max 1 (ψ uN))
        (SetTheory.app M natzero) fun _ =>
        pi (ψ uN)
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          SetTheory.app M natzero)
      (F := fun M => SetTheory.lam (Nat.max 1 (ψ uN))
        (SetTheory.app M natzero) fun z =>
        SetTheory.lam (ψ uN)
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun _s => z)
      (fun M hM' => by
        rw [hSspEq M]
        exact lam_mem (V := V) fun z hz' =>
          lam_mem (V := V) fun s hs' => hz')
      (fun M hM' => hT2 M hM')
    rw [h1]
    have h2 := app_lam (v := Nat.max 1 (ψ uN)) (a := zv)
      (A := SetTheory.app Mv natzero) hz
      (B := fun _ => pi (ψ uN)
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (natsucc n)) fun _ =>
        SetTheory.app Mv natzero)
      (F := fun z => SetTheory.lam (ψ uN)
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
        fun _s => z)
      (fun z hz' => by
        rw [hSspEq Mv]
        exact lam_mem (V := V) fun s hs' => hz')
      (fun _ _ => hT3 Mv hM)
    rw [h2]
    rw [hSspEq Mv]
    exact (app_lam (v := ψ uN) (a := sv)
      (A := pi (ψ uN) omega fun n =>
        pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (natsucc n)) hs
      (B := fun _ => SetTheory.app Mv natzero)
      (F := fun _s => zv)
      (fun _ _ => hz)
      (fun _ _ => hMfib natzero natzero_mem)).symm

/-- The fold equation of `Nat.rec`'s successor rule. -/
theorem natSucc_iota {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    (hfindR : env.find? (natName.str "rec") = some natRecA)
    (hvalR : ∀ ψ' : Name → Nat, cval (natName.str "rec") ψ' = natRecVal V ψ')
    {Mv zv sv nv : V}
    (hM : Mv ∈ˢ pi (ψ uN + 1) omega fun _ => univ (ψ uN))
    (hz : zv ∈ˢ SetTheory.app Mv natzero)
    (hs : sv ∈ˢ pi (ψ uN) omega fun n =>
      pi (ψ uN) (SetTheory.app Mv n) fun _ =>
        SetTheory.app Mv (natsucc n))
    (hn : nv ∈ˢ omega) :
    ∃ R, interpClosed V cval env ψ natRecSuccRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (natRecVal V ψ) Mv) zv) sv) (natsucc nv) =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app R Mv) zv)
        sv) nv := by
  refine ⟨_, interp_natRecSucc_rhs hfindN hvalN hfindZ hvalZ hfindSc hvalSc
    hfindR hvalR, ?_⟩
  rw [natRecVal_fold hM hz hs (natsucc_mem hn), natrec_succ zv sv hn]
  have hMfib : ∀ n, n ∈ˢ omega → SetTheory.app Mv n ∈ˢ univ (ψ uN) :=
    fun n hn' => app_mem hM hn' (fun _ _ => univ_mem_univ (ψ uN))
  have hstep : ∀ k, k ∈ˢ omega → ∀ ih, ih ∈ˢ SetTheory.app Mv k →
      SetTheory.app (SetTheory.app sv k) ih ∈ˢ
        SetTheory.app Mv (natsucc k) := by
    intro k hk ih hih
    have hsfib : ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro n hn'
      have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib n hn')
        (fun _ _ => hMfib (natsucc n) (natsucc_mem hn'))
      by_cases hu : ψ uN = 0
      · simpa [hu] using this
      · simpa [hu, Nat.max_self] using this
    exact app_mem (app_mem hs hk hsfib) hih
      (fun _ _ => hMfib (natsucc k) (natsucc_mem hk))
  by_cases h0 : ψ uN = 0
  · -- Prop collapse: the rhs value is the proof point, and so is the
    -- applied minor premise
    have hR : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.lam (enM (ψ uN))
          (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
          SetTheory.lam (enZ (ψ uN)) (SetTheory.app M natzero) fun z =>
            SetTheory.lam (en1U (ψ uN))
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              fun s =>
              SetTheory.lam (ψ uN) omega fun n =>
                SetTheory.app (SetTheory.app s n)
                  (SetTheory.app (SetTheory.app (SetTheory.app
                    (SetTheory.app (natRecVal V ψ) M) z) s) n)) Mv) zv)
        sv) nv = pt := by
      rw [show enM (ψ uN) = 0 from by rw [enM_eq, if_pos h0]]
      rw [lam_zero, app_pt, app_pt, app_pt, app_pt]
    rw [hR]
    exact mem_univ_zero (h0 ▸ hMfib (natsucc nv) (natsucc_mem hn))
      (hstep nv hn (natrec zv sv nv) (natrec_mem hz hstep hn))
  · -- data levels: the rhs value applies the minor premise to `n` and
    -- the recursive call
    rw [show enM (ψ uN) = Nat.max 1 (ψ uN) from by rw [enM_eq, if_neg h0],
      show enZ (ψ uN) = Nat.max 1 (ψ uN) from by rw [enZ_eq, if_neg h0],
      show en1U (ψ uN) = Nat.max 1 (ψ uN) from by rw [en1U_eq, if_neg h0],
      enUU_eq]
    have hSspEq : ∀ M : V,
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) := fun M =>
      pi_congr fun n hn' => by rw [natSuccVal_app hn']
    have hsfib : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro M hM' n hn'
      have hMfib' : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ uN) :=
        fun k hk => app_mem hM' hk (fun _ _ => univ_mem_univ (ψ uN))
      have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib' n hn')
        (fun _ _ => hMfib' (natsucc n) (natsucc_mem hn'))
      rw [if_neg h0,
        show Nat.max (ψ uN) (ψ uN) = ψ uN from Nat.max_self _] at this
      exact this
    have hbody : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ z, z ∈ˢ SetTheory.app M natzero →
        ∀ s, s ∈ˢ (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) →
        ∀ n, n ∈ˢ omega →
        SetTheory.app (SetTheory.app s n)
          (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (natRecVal V ψ) M) z) s) n) ∈ˢ
          SetTheory.app M (natsucc n) := by
      intro M hM' z hz' s hs' n hn'
      rw [natRecVal_fold hM' hz' hs' hn']
      have hMfib' : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ uN) :=
        fun k hk => app_mem hM' hk (fun _ _ => univ_mem_univ (ψ uN))
      have hstep' : ∀ k, k ∈ˢ omega → ∀ ih, ih ∈ˢ SetTheory.app M k →
          SetTheory.app (SetTheory.app s k) ih ∈ˢ
            SetTheory.app M (natsucc k) := by
        intro k hk ih hih
        exact app_mem (app_mem hs' hk (hsfib M hM')) hih
          (fun _ _ => hMfib' (natsucc k) (natsucc_mem hk))
      exact hstep' n hn' _ (natrec_mem hz' hstep' hn')
    have hT4 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun n => SetTheory.app M (natsucc n)) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => SetTheory.app M (natsucc n))
        (omega_mem_univ (V := V))
        (fun n hn' => app_mem hM' (natsucc_mem hn')
          (fun _ _ => univ_mem_univ (ψ uN)))
      rw [if_neg h0] at this
      exact this
    have hSsp : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) ∈ˢ univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n))
        (omega_mem_univ (V := V))
        (fun n hn' => hsfib M hM' n hn')
      rw [if_neg h0] at this
      exact this
    have hwne : Nat.max 1 (ψ uN) ≠ 0 := max_ne_zero_l (by decide)
    have hT3 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun n => SetTheory.app M (natsucc n)) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (ψ uN) omega fun n =>
          SetTheory.app M (natsucc n))
        (hSsp M hM') (fun _ _ => hT4 M hM')
      rw [if_neg hwne, show Nat.max (Nat.max 1 (ψ uN)) (Nat.max 1 (ψ uN)) =
        Nat.max 1 (ψ uN) from Nat.max_self _] at this
      exact this
    have hT2 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun _ =>
            pi (ψ uN) omega fun n => SetTheory.app M (natsucc n)) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun n => SetTheory.app M (natsucc n))
        (app_mem hM' natzero_mem (fun _ _ => univ_mem_univ (ψ uN)))
        (fun _ _ => hT3 M hM')
      rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
      exact this
    have h1 := app_lam (v := Nat.max 1 (ψ uN)) (a := Mv)
      (A := pi (ψ uN + 1) omega fun _ => univ (ψ uN)) hM
      (B := fun M => pi (Nat.max 1 (ψ uN))
        (SetTheory.app M natzero) fun _ =>
        pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun n => SetTheory.app M (natsucc n))
      (F := fun M => SetTheory.lam (Nat.max 1 (ψ uN))
        (SetTheory.app M natzero) fun z =>
        SetTheory.lam (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun s =>
          SetTheory.lam (ψ uN) omega fun n =>
            SetTheory.app (SetTheory.app s n)
              (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (natRecVal V ψ) M) z) s) n))
      (fun M hM' => by
        rw [hSspEq M]
        exact lam_mem (V := V) fun z hz' =>
          lam_mem (V := V) fun s hs' =>
            lam_mem (V := V) fun n hn' =>
              hbody M hM' z hz' s hs' n hn')
      (fun M hM' => hT2 M hM')
    rw [h1]
    have h2 := app_lam (v := Nat.max 1 (ψ uN)) (a := zv)
      (A := SetTheory.app Mv natzero) hz
      (B := fun _ => pi (Nat.max 1 (ψ uN))
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (natsucc n)) fun _ =>
        pi (ψ uN) omega fun n => SetTheory.app Mv (natsucc n))
      (F := fun z => SetTheory.lam (Nat.max 1 (ψ uN))
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
        fun s =>
        SetTheory.lam (ψ uN) omega fun n =>
          SetTheory.app (SetTheory.app s n)
            (SetTheory.app (SetTheory.app (SetTheory.app
              (SetTheory.app (natRecVal V ψ) Mv) z) s) n))
      (fun z hz' => by
        rw [hSspEq Mv]
        exact lam_mem (V := V) fun s hs' =>
          lam_mem (V := V) fun n hn' =>
            hbody Mv hM z hz' s hs' n hn')
      (fun _ _ => hT3 Mv hM)
    rw [h2]
    rw [hSspEq Mv]
    have h3 := app_lam (v := Nat.max 1 (ψ uN)) (a := sv)
      (A := pi (ψ uN) omega fun n =>
        pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (natsucc n)) hs
      (B := fun _ => pi (ψ uN) omega fun n =>
        SetTheory.app Mv (natsucc n))
      (F := fun s => SetTheory.lam (ψ uN) omega fun n =>
        SetTheory.app (SetTheory.app s n)
          (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (natRecVal V ψ) Mv) zv) s) n))
      (fun s hs' => lam_mem (V := V) fun n hn' =>
        hbody Mv hM zv hz s hs' n hn')
      (fun _ _ => hT4 Mv hM)
    rw [h3]
    have h4 := app_lam (v := ψ uN) (a := nv) (A := omega) hn
      (B := fun n => SetTheory.app Mv (natsucc n))
      (F := fun n => SetTheory.app (SetTheory.app sv n)
        (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (natRecVal V ψ) Mv) zv) sv) n))
      (fun n hn' => hbody Mv hM zv hz sv hs n hn')
      (fun n hn' => hMfib (natsucc n) (natsucc_mem hn'))
    rw [h4, natRecVal_fold hM hz hs hn]

end Setlec
