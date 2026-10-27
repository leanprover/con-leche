module

public import ConLeche.Model.Levels
public import ConLeche.Semantics.BasisRules
import ConLeche.Verify.Denote.Inst

import ConLeche.Model.BasisLfp
import ConLeche.Model.Cover
public section

/-!
# The remaining basis blocks, P tier (task #161, ENDGAME G)

`Model/BasisEmpty.lean` covers `BasisStepPB`'s `emptyK` branch; this
file carries the same recipe across the other blocks in one file — the
shared leaf-reading kit below is used at every one of them.

Three pieces of kit that `BasisEmpty.lean` does not need, because
`Empty` binds no level parameter and `Empty.rec` has no rules:

* `denote_pinned_const` — a *leveled* pinned leaf's reading;
* `denote_instLevels` (`Model/Levels.lean`) — so that a recursor
  row's instantiated subjects (`RecRuleLaw` reads
  `rhs.instantiateLevelParams` and `cv.type.instantiateLevelParams`)
  are the *raw* readings at a substituted assignment.  One reading
  lemma per constant then serves both `EnvModelM.type_reads` and the
  row's `TVa`;
* `declStep_preserves_of_basis_rec_cons` (`Model/BasisStep.lean`) — the six
  collapsed rows at a recursor cons, whose seventh is bespoke.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule uN u1N vN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## The leaf kit

A pinned leaf's reading at a constant that binds levels. -/

/-- **A stored pinned constant's reading, at a level list.**  The
extension's fresh leaf is stepped over by `acvalWith_ne`, the prefix
lookup by `Env.find?_cons`, and the leaf itself is
`EnvModel.acval_pinned`. -/
theorem denote_pinned_const {m : EnvModel V env}
    {c₀ : ConstantInfo} {A : (Name → Nat) → Term}
    {n : Name} {ci : ConstantInfo} {ψ : Name → Nat} {ls : List Level}
    (hne : ¬ c₀.name = n)
    (hf : env.find? n = some ci)
    (hres : ConLeche.reservedBasisNames.contains n = true)
    (hlen : ls.length = ci.toConstantVal.levelParams.length)
    {c : ConLeche.Term.BConst} {us : List Nat}
    (hpd : ConLeche.Verify.pinnedStructT n
      (Level.substFn ψ ci.toConstantVal.levelParams ls)
        = some (Term.const c us)) (d : Nat) :
    denote (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts, env.tables⟩ ψ d
        (.const n ls) = some (Term.const c us) := by
  have hf' : (⟨c₀ :: env.consts, env.tables⟩ : Env).find? n = some ci := by
    rw [ConLeche.Env.find?_cons, ite_eq_right hne]; exact hf
  rw [denote_const hf' hlen, acvalWith_ne (fun h => hne h.symm),
    EnvModel.acval_pinned m hf hres hpd]

/-! ### Lift-then-instantiate absorption

`TeleFitPA` peels a `.pi` by `B.inst a`, so a telescope domain that
mentions an *earlier* argument arrives as that argument's reading
lifted past the intervening binders and then instantiated.  The two
instances the basis recursors' step spaces need. -/

/-- The general absorption: lifting past `k + 1` binders and
instantiating at `k` shifts the environment down by `k`. -/
theorem interp_liftN_succ_inst (e a : Term) (k : Nat)
    (ρ : Nat → V) :
    interp V ρ ((e.liftN (k + 1) 0).inst a k)
      = interp V (fun i => ρ (i + k)) e := by
  rw [interp_inst, interp_liftN]
  congr 1
  funext i
  show (instE k (interp V (shiftE k 0 ρ) a) ρ) (if i < 0 then i
      else i + (k + 1)) = ρ (i + k)
  rw [ite_eq_right (Nat.not_lt_zero i)]
  show (if i + (k + 1) < k then ρ (i + (k + 1))
    else if i + (k + 1) = k then _ else ρ (i + (k + 1) - 1)) = ρ (i + k)
  rw [ite_eq_right (by omega), ite_eq_right (by omega),
    show i + (k + 1) - 1 = i + k from by omega]

theorem interp_liftN2_inst1 (e a : Term) (x : V) (ρ : Nat → V) :
    interp V (cons x ρ) ((e.liftN 2 0).inst a 1) = interp V ρ e := by
  rw [interp_liftN_succ_inst (k := 1)]
  rfl

theorem interp_liftN3_inst2 (e a : Term) (x y : V) (ρ : Nat → V) :
    interp V (cons y (cons x ρ)) ((e.liftN 3 0).inst a 2)
      = interp V ρ e := by
  rw [interp_liftN_succ_inst (k := 2)]
  rfl

/-! ## `Nat`

Four constants, two firing rules, and the block's one bespoke row that
is not a firing law: `nat_heads`, at the cons where the literal guard
*becomes* true.  The level question does not arise at the constructors
— `Nat.zero` and `Nat.succ` bind no level parameter — so a fired rule's
`usj` is forced to `[]`. -/

section Nat

open ConLeche (natA natZeroA natSuccA natRecA natName natZeroName
  natSuccName)

variable {m : EnvModel V env} {A : (Name → Nat) → Term}

/-- `Nat`'s type reading: `Sort 1`, `BConst.typeAV .nat []` on the
nose. -/
theorem denote_natA_type
    {acval : Name → (Name → Nat) → Term} (ψ : Name → Nat) :
    denote acval ⟨natA :: env.consts, env.tables⟩ ψ 0 natA.toConstantVal.type
      = some (BConst.typeAV .nat []) := by
  rw [show natA.toConstantVal.type = Expr.sort (.succ .zero) from rfl,
    denote_sort]
  rfl

/-- The pinned `Nat` leaf at an extension. -/
theorem denote_natLeaf {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = natName)
    (hN : env.find? natName = some natA) (d : Nat) :
    denote (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts, env.tables⟩ ψ d
        (.const natName []) = some (Term.const .nat []) := by
  refine denote_pinned_const (m := m) hne hN (by decide) (by rfl) ?_ d
  simp +decide [ConLeche.Verify.pinnedStructT]

/-- `Nat.zero`'s type reading. -/
theorem denote_natZeroA_type (ψ : Name → Nat)
    (hN : env.find? natName = some natA) :
    denote (acvalWith m.acval natZeroA.name A)
        ⟨natZeroA :: env.consts, env.tables⟩ ψ 0 natZeroA.toConstantVal.type
      = some (BConst.typeAV .natZero []) := by
  rw [show natZeroA.toConstantVal.type = Expr.const natName [] from rfl]
  exact denote_natLeaf (m := m) (A := A) ψ (by decide) hN 0

/-- `Nat.succ`'s type reading — one binder, `Nat → Nat`.  Stated at *any* extension whose cons is
not `Nat`, because the `Nat.rec` row reads it too (its rule's
constructor is `Nat.succ`). -/
theorem denote_natSuccTy {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = natName)
    (hN : env.find? natName = some natA) :
    denote (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts, env.tables⟩ ψ 0
        natSuccA.toConstantVal.type
      = some (.pi (.const .nat [])
          (.const .nat [])) := by
  have hNc := fun d => denote_natLeaf (m := m) (A := A) (c₀ := c₀)
    ψ hne hN d
  rw [show natSuccA.toConstantVal.type
      = Expr.forallE (.const natName [])
          (.const natName []) from rfl]
  simp [denote_forallE, Expr.instantiate1, hNc]

theorem denote_natSuccA_type (ψ : Name → Nat)
    (hN : env.find? natName = some natA) :
    denote (acvalWith m.acval natSuccA.name A)
        ⟨natSuccA :: env.consts, env.tables⟩ ψ 0 natSuccA.toConstantVal.type
      = some (.pi (.const .nat [])
          (.const .nat [])) :=
  denote_natSuccTy (m := m) (A := A) ψ (by decide) hN

/-- The reading of `Nat.succ`'s type is its spelled type. -/
theorem natSuccA_reading_eq :
    (Term.pi (.const .nat []) (.const .nat []))
      = BConst.typeAV .natSucc [] := rfl

/-- The three pinned `Nat` leaves at the `Nat.rec` extension. -/
theorem denote_natRec_leaves (ψ : Name → Nat)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    (∀ d : Nat, denote (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts, env.tables⟩ ψ d (.const natName [])
        = some (Term.const .nat [])) ∧
    (∀ d : Nat, denote (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts, env.tables⟩ ψ d (.const natZeroName [])
        = some (Term.const .natZero [])) ∧
    (∀ d : Nat, denote (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts, env.tables⟩ ψ d (.const natSuccName [])
        = some (Term.const .natSucc [])) := by
  refine ⟨fun d => denote_natLeaf (m := m) (A := A) ψ (by decide) hN d,
    fun d => ?_, fun d => ?_⟩
  · refine denote_pinned_const (m := m) (by decide) hZ (by decide)
      (by rfl) ?_ d
    simp +decide [ConLeche.Verify.pinnedStructT]
  · refine denote_pinned_const (m := m) (by decide) hS (by decide)
      (by rfl) ?_ d
    simp +decide [ConLeche.Verify.pinnedStructT]

/-- **`Nat.rec`'s type reading.**  Seven binders; six carry
`.ifAllZero [u]` and the motive's domain carries `.never`. -/
theorem denote_natRecA_type (ψ : Name → Nat)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denote (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts, env.tables⟩ ψ 0 natRecA.toConstantVal.type
      = some (.pi (.pi (.const .nat []) (.sort (ψ uN)))
          (.pi (.app (.bvar 0) (.const .natZero []))
            (.pi (.pi (.const .nat [])
                (.pi (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 3)
                    (.app (.const .natSucc []) (.bvar 1)))))
              (.pi (.const .nat [])
                (.app (.bvar 3) (.bvar 0)))))) := by
  obtain ⟨hNc, hZc, hSc⟩ :=
    denote_natRec_leaves (m := m) (A := A) ψ hN hZ hS
  rw [show natRecA.toConstantVal.type
      = Expr.forallE
          (Expr.forallE (.const natName [])
            (.sort (.param uN)))
          (Expr.forallE
            (.app (.bvar 0) (.const natZeroName []))
            (Expr.forallE
              (Expr.forallE (.const natName [])
                (Expr.forallE
                  (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 3)
                    (.app (.const natSuccName []) (.bvar 1)))))
              (Expr.forallE (.const natName [])
                (.app (.bvar 3) (.bvar 0))))) from rfl]
  simp [denote_forallE, denote_sort, denote_app, denote_fvar,
    Expr.instantiate1, hNc, hZc, hSc, Level.eval]

/-- The reading of `Nat.rec`'s type is its spelled type. -/
theorem natRecA_reading_eq (ψ : Name → Nat) :
    (Term.pi (.pi (.const .nat []) (.sort (ψ uN)))
      (.pi (.app (.bvar 0) (.const .natZero []))
        (.pi (.pi (.const .nat [])
            (.pi (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3)
                (.app (.const .natSucc []) (.bvar 1)))))
          (.pi (.const .nat [])
            (.app (.bvar 3) (.bvar 0))))))
      = BConst.typeAV .natRec [ψ uN] := rfl

/-! ### The installs

The first three conses are exactly the three names `nat_heads`'s guard
reads, so `natHeads_cons_offNat` is unavailable at every one of them
(`declStep_preserves_of_basis_cons_gen`).  At `Nat` and `Nat.zero` the guard is
still *false* — `Nat.succ` is not stored yet — and the row is vacuous;
at `Nat.succ` the guard becomes true and the row is the block's one
bespoke non-firing obligation, two memberships. -/

/-- **`Nat`, installed at the P tier.** -/
theorem extendNat (mp : EnvModelM V μ env)
    (hfresh : env.find? natName = none)
    (hguard : ConLeche.natLitSupported ⟨natA :: env.consts, env.tables⟩ = false)
    (hwf : EnvWF ⟨natA :: env.consts, env.tables⟩) :
    CoverTo mp [] ⟨natA :: env.consts, env.tables⟩ [natName] := by
  -- the pinned block's lfp clause is recorded at its last constructor's
  -- cons (`extendNatSucc`: the clause's `ctor` reads the constructors' leaves)
  refine coverTo_pend hfresh (declStep_preserves_of_basis_cons_gen mp
    (A := fun _ => Term.const .nat []) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT natA.name ψ
          = some (Term.const .nat []) from rfl] at hp
        rw [← Option.some.inj hp]) (fun _ _ _ _ h => nomatch h))
    (fun _ _ _ => rfl)
    (fun _ _ => trivial)
    (fun ψ => ⟨_, denote_natA_type ψ⟩) ?_ ?_ ?_ ?_
    (hind := indStrictHead_cons (ab := fun _ => []) (s := fun _ => 1)
      (fun ψ => denote_natA_type ψ) fun _ _ ρ vs hsp => by
        cases vs with
        | nil => exact strict_omega
        | cons _ _ => exact hsp.elim))
  · intro ψ ta h ρ
    rw [denote_natA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact WellDenotedTy_bconst_type V .nat [] ρ
  · intro ψ ta h ρ
    rw [denote_natA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval_mem_type V .nat [] ρ
  · intro _ _ _ hg
    rw [hguard] at hg
    exact nomatch hg
  · exact fun m₂ hac φ => recRules_cons_fresh mp (c₀ := natA) hfresh
      (fun _ _ _ _ h => nomatch h) m₂ hac φ

/-- **`Nat.zero`, installed at the P tier.** -/
theorem extendNatZero (mp : EnvModelM V μ env)
    (hN : env.find? natName = some natA)
    (hfresh : env.find? natZeroName = none)
    (hguard : ConLeche.natLitSupported ⟨natZeroA :: env.consts, env.tables⟩ = false)
    (hwf : EnvWF ⟨natZeroA :: env.consts, env.tables⟩) {ex : List Name} (hNex : natName ∈ ex) :
    CoverTo mp ex ⟨natZeroA :: env.consts, env.tables⟩ ex := by
  have hty := fun ψ =>
    denote_natZeroA_type (m := mp.base2)
      (A := fun _ => Term.const .natZero []) ψ hN
  refine coverTo_cons hfresh (fun _ _ h => nomatch h)
    (hhead := hhead_ctor (c₀ := natZeroA) rfl rfl rfl (Or.inl hNex))
    (declStep_preserves_of_basis_cons_gen mp
    (A := fun _ => Term.const .natZero []) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT natZeroA.name ψ
          = some (Term.const .natZero []) from rfl] at hp
        rw [← Option.some.inj hp]) (fun _ _ _ _ h => nomatch h))
    (fun _ _ _ => rfl)
    (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_ ?_)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact WellDenotedTy_bconst_type V .natZero [] ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval_mem_type V .natZero [] ρ
  · intro _ _ _ hg
    rw [hguard] at hg
    exact nomatch hg
  · exact fun m₂ hac φ => recRules_cons_fresh mp (c₀ := natZeroA)
      hfresh (fun _ _ _ _ h => nomatch h) m₂ hac φ

/-- **`Nat.succ`, installed at the P tier** — the cons where the
literal guard becomes true, so `nat_heads` is bespoke here and nowhere
else.  Its content is `natzero_mem` and `natSuccV_mem`. -/
theorem extendNatSucc (mp : EnvModelM V μ env)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hfresh : env.find? natSuccName = none)
    (hwf : EnvWF ⟨natSuccA :: env.consts, env.tables⟩) :
    CoverTo mp [natName] ⟨natSuccA :: env.consts, env.tables⟩ [] := by
  have hty := fun ψ =>
    denote_natSuccA_type (m := mp.base2)
      (A := fun _ => Term.const .natSucc []) ψ hN
  -- the pinned block's lfp clause, recorded at its last constructor's cons
  -- (the constructors' leaves are read by `ctor`)
  have hNl0 : ∀ ψ : Name → Nat, mp.base2.acval natName ψ = Term.const .nat [] :=
    fun ψ => EnvModel.acval_pinned mp.base2 hN (by decide) rfl
  have hZl0 : ∀ ψ : Name → Nat, mp.base2.acval natZeroName ψ = Term.const .natZero [] :=
    fun ψ => EnvModel.acval_pinned mp.base2 hZ (by decide) rfl
  refine coverTo_addLfp (D := natLfp natName natZeroName natSuccName) (hag := fun _ h => Agrees.cons hfresh h)
    (hL := natLfp_clause
      (fun ψ ρ => by rw [acvalWith_ne (by decide), hNl0]; rfl)
      (fun ψ ρ => by rw [acvalWith_ne (by decide), hZl0]; simp [interp_const, bval, natzero])
      (fun ψ ρ => by
        rw [show natSuccName = natSuccA.name from rfl, acvalWith_self]; rfl))
    (hst := lfp0_stored_of
      ⟨_, _, by rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN⟩
      (fun j hj => by
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · exact ⟨_, _, _, by
            show (⟨natSuccA :: env.consts, env.tables⟩ : ConLeche.Env).find? natZeroName = _
            rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hZ⟩
        · exact ⟨_, _, _, by
            show (⟨natSuccA :: env.consts, env.tables⟩ : ConLeche.Env).find? natSuccA.name = _
            rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl⟩))
    (hrd := lfp0_reads (by rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN)
      (fun ψ => by show denote _ _ _ 0 (.sort _) = _; rw [denote_sort]; rfl))
    (hcaps := lfp0_caps (by rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN)
      (fun _ h => absurd h Nat.one_ne_zero) (fun h => absurd h (by decide))
      (fun j hj => by
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · exact ⟨_, _, _, by
            show (⟨natSuccA :: env.consts, env.tables⟩ : ConLeche.Env).find? natZeroName = _
            rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hZ, _, [], rfl⟩
        · exact ⟨_, _, _, by
            show (⟨natSuccA :: env.consts, env.tables⟩ : ConLeche.Env).find? natSuccA.name = _
            rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl, _, [], rfl⟩))
    (hrdC := lfp0_ctorReads (by rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN)
      (fun ψ => ⟨_, by show denote _ _ _ 0 (.sort _) = _; rw [denote_sort]⟩) fun j hj => by
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · refine ⟨natZeroA.toConstantVal, 0, ?_, rfl,
          ⟨natA.toConstantVal, _, by rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN,
            rfl⟩,
          .fvar 0 (.sort .zero), by decide, by decide, fun ψ => ⟨rfl, [], ?_, rfl⟩⟩
        · show (⟨natSuccA :: env.consts, env.tables⟩ : ConLeche.Env).find? natZeroName = _
          rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; rw [hZ]; rfl
        · show denote _ _ _ 1 (.fvar 0 (.sort .zero)) = _
          rw [denote_fvar]; rfl
      · refine ⟨natSuccA.toConstantVal, 1, ?_, rfl,
          ⟨natA.toConstantVal, _, by rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN,
            rfl⟩,
          .forallE (.fvar 0 (.sort .zero)) (.fvar 0 (.sort .zero)), by decide,
          by decide, fun ψ => ⟨rfl, [.bvar 0], ?_, rfl⟩⟩
        · show (⟨natSuccA :: env.consts, env.tables⟩ : ConLeche.Env).find? natSuccA.name = _
          rw [ConLeche.Env.find?_cons, ite_eq_left rfl]; rfl
        · show denote _ _ _ 1 (.forallE (.fvar 0 (.sort .zero)) (.fvar 0 (.sort .zero))) = _
          simp [denote_forallE, ConLeche.Expr.instantiate1, denote_fvar, mkPisAV])
    (hnd := nodup_one _) (hlen := rfl)
    (hall := lfpAll_one (n := natName) (c := natA) rfl rfl
      (by rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN)
      (fun _ _ h => by injection h with _ h; subst h; rfl))
    (hown := lfpOwn_one (T := natName)
      (cs := [(natZeroA.toConstantVal, 0, 0), (natSuccA.toConstantVal, 0, 1)]) rfl rfl
      (by rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN)
      (by
        show List.filterMap (ctorLook (ConLeche.Env.find? ⟨natSuccA :: env.consts, env.tables⟩) natName)
          [natZeroA.name, natSuccA.name] = _
        have hz : ConLeche.Env.find? ⟨natSuccA :: env.consts, env.tables⟩ natZeroA.name = some natZeroA := by
          rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hZ
        simp only [List.filterMap_cons, List.filterMap_nil, ctorLook, hz,
          ConLeche.Env.find?_cons_self, Option.bind_some,
          ctorEntry_self (c₀ := natSuccA) (T := natName) rfl rfl rfl,
          ctorEntry_self (c₀ := natZeroA) (T := natName) rfl rfl rfl]
        rfl)
      ⟨0, [(natZeroA.toConstantVal, 0), (natSuccA.toConstantVal, 1)], rfl, rfl, fun j hj => by
        rcases (show j = 0 ∨ j = 1 by simp at hj; omega) with rfl | rfl
        · show (⟨natSuccA :: env.consts, env.tables⟩ : ConLeche.Env).find? natZeroName = _
          rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; rw [hZ]; rfl
        · exact ConLeche.Env.find?_cons_self natSuccA env⟩
      (fun _ h => by simp [nestPick] at h) (by decide)
      (fun nP' L h j hj => by
        simp only [nestPick, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases (show j = 0 ∨ j = 1 by simp at hj; omega) with rfl | rfl
        · exact ⟨_, [], rfl, fun _ => rfl⟩
        · exact ⟨_, [], rfl, fun _ => rfl⟩))
    (hex := filter_not_mem_self _)
    (coverA_cons hfresh (fun _ h => h) (fun _ _ h => nomatch h)
      (hhead := hhead_ctor (c₀ := natSuccA) rfl rfl rfl (Or.inl List.mem_cons_self)) <|
      declStep_preserves_of_basis_cons_gen mp
    (A := fun _ => Term.const .natSucc []) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT natSuccA.name ψ
          = some (Term.const .natSucc []) from rfl] at hp
        rw [← Option.some.inj hp]) (fun _ _ _ _ h => nomatch h))
    (fun _ _ _ => rfl)
    (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_ ?_)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [natSuccA_reading_eq]
    exact WellDenotedTy_bconst_type V .natSucc [] ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [natSuccA_reading_eq]
    exact bval_mem_type V .natSucc [] ρ
  · -- `nat_heads`, bespoke: the three leaves are the two prefix pins
    -- and the fresh one
    intro m₂ hac φ _ ρ
    have hZl : m₂.acval natZeroName (Level.substFn φ [] [])
        = Term.const .natZero [] := by
      rw [hac, acvalWith_ne (by decide)]
      refine EnvModel.acval_pinned mp.base2 hZ (by decide) ?_
      simp +decide [ConLeche.Verify.pinnedStructT]
    have hNl : m₂.acval natName (Level.substFn φ [] [])
        = Term.const .nat [] := by
      rw [hac, acvalWith_ne (by decide)]
      refine EnvModel.acval_pinned mp.base2 hN (by decide) ?_
      simp +decide [ConLeche.Verify.pinnedStructT]
    have hSl : m₂.acval natSuccName (Level.substFn φ [] [])
        = Term.const .natSucc [] := by
      rw [hac, show natSuccName = natSuccA.name from rfl,
        acvalWith_self]
    rw [hZl, hNl, hSl]
    exact ⟨by simpa [interp_const, bval] using
        (natzero_mem : (natzero : V) ∈ˢ omega),
      by simpa [interp_const, bval] using natSuccV_mem V,
      by simpa [interp_const, bval] using (IsTy_omega : IsTy (omega : V))⟩
  · exact fun m₂ hac φ => recRules_cons_fresh mp (c₀ := natSuccA)
      hfresh (fun _ _ _ _ h => nomatch h) m₂ hac φ

/-! ### The two firing rules

The three telescope domains, named once.  Their readings are
`SetModel/Value.lean`'s `natMotiveSpace` and `natStepSpace`, the spaces
`natRecV` abstracts over. -/

/-- The motive binder's domain reading. -/
def natMotiveTy (ψ : Name → Nat) : Term :=
  .pi (.const .nat []) (.sort (ψ uN))

/-- The step binder's domain reading. -/
def natStepTy : Term :=
  .pi (.const .nat [])
    (.pi (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 3) (.app (.const .natSucc []) (.bvar 1))))

theorem natMotiveTy_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natMotiveTy ψ) = natMotiveSpace V (ψ uN) := by
  rw [natMotiveTy, interp_pi, natMotiveSpace]
  rfl

/-- The step binder's domain reading: the step space. -/
theorem natStepTy_interp (ρ : Nat → V) (M z : V) :
    interp V (cons z (cons M ρ)) (natStepTy) = natStepSpace V M := by
  rw [natStepTy, interp_pi]
  simp only [interp_const, bval]
  refine piV_congr fun n hn => ?_
  rw [interp_pi]
  simp only [interp_app, interp_bvar, interp_const, cons, bval]
  exact piV_congr fun _ _ => by rw [natSuccV_app V hn]

/-- The `zero` rule's RHS reading. -/
def natZeroRa (ψ : Name → Nat) : Term :=
  .lam (natMotiveTy ψ)
    (.lam (.app (.bvar 0) (.const .natZero []))
      (.lam (natStepTy) (.bvar 1)))

/-- The `succ` rule's RHS reading — the recursive occurrence is the
*fresh* leaf, so it reads to `.const .natRec [ψ u]`. -/
def natSuccRa (ψ : Name → Nat) : Term :=
  .lam (natMotiveTy ψ)
    (.lam (.app (.bvar 0) (.const .natZero []))
      (.lam (natStepTy)
        (.lam (.const .nat [])
          (.app (.app (.bvar 1) (.bvar 0))
            (.app (.app (.app (.app (.const .natRec [ψ uN]) (.bvar 3))
              (.bvar 2)) (.bvar 1)) (.bvar 0))))))

theorem denote_natRec_zeroRhs (ψ : Name → Nat)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denote (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts, env.tables⟩ ψ 0 natRecZeroRule.rhs
      = some (natZeroRa ψ) := by
  obtain ⟨hNc, hZc, hSc⟩ :=
    denote_natRec_leaves (m := m) (A := A) ψ hN hZ hS
  rw [show natRecZeroRule.rhs = Expr.lam
      (Expr.forallE (.const natName [])
        (.sort (.param uN)))
      (Expr.lam
        (.app (.bvar 0) (.const natZeroName []))
        (Expr.lam
          (Expr.forallE (.const natName [])
            (Expr.forallE
              (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))))
          (.bvar 1))) from rfl]
  simp [denote_lam, denote_forallE, denote_sort, denote_app,
    denote_fvar, Expr.instantiate1, hNc, hZc, hSc, Level.eval,
    natZeroRa, natMotiveTy, natStepTy]

theorem denote_natRec_succRhs (ψ : Name → Nat)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denote (acvalWith m.acval natRecA.name
        (fun ψ => Term.const .natRec [ψ uN]))
        ⟨natRecA :: env.consts, env.tables⟩ ψ 0 natRecSuccRule.rhs
      = some (natSuccRa ψ) := by
  obtain ⟨hNc, hZc, hSc⟩ :=
    denote_natRec_leaves (m := m)
      (A := fun ψ => Term.const .natRec [ψ uN]) ψ hN hZ hS
  have hRc : ∀ d : Nat,
      denote (acvalWith m.acval natRecA.name
          (fun ψ => Term.const .natRec [ψ uN]))
        ⟨natRecA :: env.consts, env.tables⟩ ψ d
        (.const (natName.str "rec") [.param uN])
        = some (Term.const .natRec [ψ uN]) := by
    intro d
    have hf : (⟨natRecA :: env.consts, env.tables⟩ : Env).find? (natName.str "rec")
        = some natRecA := by
      rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl
    rw [denote_const hf (by rfl),
      show natName.str "rec" = natRecA.name from rfl, acvalWith_self]
    show some (Term.const .natRec
      [Level.substFn ψ natRecA.toConstantVal.levelParams
        [Level.param uN] uN]) = _
    rw [show Level.substFn ψ natRecA.toConstantVal.levelParams
        [Level.param uN] uN = ψ uN from rfl]
  rw [show natRecSuccRule.rhs = Expr.lam
      (Expr.forallE (.const natName [])
        (.sort (.param uN)))
      (Expr.lam
        (.app (.bvar 0) (.const natZeroName []))
        (Expr.lam
          (Expr.forallE (.const natName [])
            (Expr.forallE
              (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))))
          (Expr.lam (.const natName [])
            (.app (.app (.bvar 1) (.bvar 0))
              (.app (.app (.app (.app
                (.const (natName.str "rec") [.param uN]) (.bvar 3))
                (.bvar 2)) (.bvar 1)) (.bvar 0)))))) from rfl]
  simp [denote_lam, denote_forallE, denote_sort, denote_app,
    denote_fvar, Expr.instantiate1, hNc, hZc, hSc, hRc, Level.eval,
    natSuccRa, natMotiveTy, natStepTy]

/-- The motive binder's domain is graded. -/
theorem natMotiveTy_wellDenoted (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenoted V ρ (natMotiveTy ψ) :=
  ⟨trivial, IsTy_omega, fun _ _ => trivial, fun _ _ => IsTy_univ _⟩

/-- The step binder's domain is graded, under a motive membership: the
fibre obligations are `natMotive_apply` at `n` and at `n + 1`. -/
theorem natStepTy_wellDenoted (ψ : Name → Nat) (ρ : Nat → V) (M z : V)
    (hM : M ∈ˢ natMotiveSpace V (ψ uN)) :
    WellDenoted V (cons z (cons M ρ)) (natStepTy) := by
  have hMn : ∀ n : V, n ∈ˢ (omega : V) → app M n ∈ˢ (univ (ψ uN) : V) :=
    fun n hn => natMotive_apply V hM hn
  have hdom : ∀ n : V,
      interp V (cons n (cons z (cons M ρ))) (.app (.bvar 2) (.bvar 0))
        = app M n := by
    intro n; simp [interp_app, interp_bvar, cons]
  have hcod : ∀ (n ih : V),
      interp V (cons ih (cons n (cons z (cons M ρ))))
          (.app (.bvar 3) (.app (.const .natSucc []) (.bvar 1)))
        = app M (app (natSuccV V) n) := by
    intro n ih; simp [interp_app, interp_bvar, interp_const, cons,
      bval]
  have hM' : M ∈ˢ piR (ψ uN + 1) (omega : V) fun _ => univ (ψ uN) := by
    rw [← piV_univ_eq_pos (Nat.succ_ne_zero _) (natzero_mem (V := V)) _ fun _ _ => ⟨_, rfl⟩]
    exact hM
  refine ⟨trivial, IsTy_omega, fun n hn => ?_, fun _ _ => IsTy_piV⟩
  have hn' : n ∈ˢ (omega : V) := by
    simpa [interp_const, bval] using hn
  refine ⟨⟨trivial, trivial, ψ uN + 1, omega, fun _ => univ (ψ uN),
      by simpa [interp_bvar, cons] using hM',
      by simpa [interp_bvar, cons] using hn',
      fun h => absurd h (Nat.succ_ne_zero _), fun _ => IsTy_omega⟩,
    by rw [hdom n]; exact IsTy_of_mem_univ (hMn n hn'),
    fun ih _ => ⟨trivial, ⟨trivial, trivial, 1, omega,
      fun _ => omega, natSuccV_mem V,
      by simpa [interp_bvar, cons] using hn',
      fun h => absurd h Nat.one_ne_zero, fun _ => IsTy_omega⟩,
      ψ uN + 1, omega, fun _ => univ (ψ uN),
      by simpa [interp_bvar, cons] using hM',
      by rw [interp_app, interp_const, interp_bvar]
         show app (natSuccV V) _ ∈ˢ _
         rw [show cons ih (cons n (cons z (cons M ρ))) 1 = n from rfl,
           natSuccV_app V hn']
         exact natsucc_mem hn',
      fun h => absurd h (Nat.succ_ne_zero _), fun _ => IsTy_omega⟩,
    fun ih _ => by
      rw [hcod n ih, natSuccV_app V hn']
      exact IsTy_of_mem_univ (hMn _ (natsucc_mem hn'))⟩

/-! ### The two RHS towers, interpreted and graded -/

theorem natZeroRa_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natZeroRa ψ)
      = lamV (natMotiveSpace V (ψ uN))
          (fun M => lamV (app M natzero)
            (fun z => lamV
              (natStepSpace V M)
              (fun _ => z))) := by
  simp only [natZeroRa, interp_lam, interp_app, interp_bvar,
    interp_const, cons, bval, natMotiveTy_interp, natStepTy_interp]

theorem natSuccRa_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natSuccRa ψ)
      = lamV (natMotiveSpace V (ψ uN))
          (fun M => lamV (app M natzero)
            (fun z => lamV
              (natStepSpace V M)
              (fun s => lamV omega
                (fun n => app (app s n)
                  (app (app (app (app (natRecV V (ψ uN)) M) z) s)
                    n))))) := by
  simp only [natSuccRa, interp_lam, interp_app, interp_bvar,
    interp_const, cons, bval, natMotiveTy_interp,
    natStepTy_interp, ConLeche.Term.lv, List.getD_cons_zero]

/-- **The recursive spine is graded**, once and for all: four
`bconst_app_data` steps at `Nat.rec`'s own `typeAV` binders, with the
four domains identified with `SetModel/Value.lean`'s spaces.  Used at
the `succ` rule, where the RHS mentions the recursor. -/
theorem natRecSpine_wellDenoted {u : Nat} (ρ : Nat → V) {e1 e2 e3 e4 : Term}
    (h1 : WellDenoted V ρ e1) (h2 : WellDenoted V ρ e2)
    (h3 : WellDenoted V ρ e3) (h4 : WellDenoted V ρ e4)
    (m1 : interp V ρ e1 ∈ˢ natMotiveSpace V u)
    (m2 : interp V ρ e2 ∈ˢ app (interp V ρ e1) natzero)
    (m3 : interp V ρ e3 ∈ˢ natStepSpace V (interp V ρ e1))
    (m4 : interp V ρ e4 ∈ˢ (omega : V)) :
    WellDenoted V ρ
      (.app (.app (.app (.app (.const .natRec [u]) e1) e2) e3) e4) := by
  have hlv : ConLeche.Term.lv [u] 0 = u := rfl
  have d1 : interp V ρ (arrowA natTyAV (.sort u))
      = natMotiveSpace V u := by
    simp only [arrowA, natTyAV, Term.lift, Term.liftN, interp_pi,
      interp_const, interp_sort, bval, natMotiveSpace]
  have d2 : ∀ a1 : V, interp V (cons a1 ρ)
      (.app (.bvar 0) natZeroAV) = app a1 natzero := by
    intro a1
    simp [natZeroAV, interp_app, interp_bvar, interp_const, cons,
      bval]
  have d3 : ∀ a1 a2 : V, interp V (cons a2 (cons a1 ρ))
      (Term.pi natTyAV (.pi (.app (.bvar 2) (.bvar 0))
        (.app (.bvar 3) (natSuccAV (.bvar 1)))))
      = natStepSpace V a1 := by
    intro a1 a2
    rw [interp_pi]
    simp only [natTyAV, interp_const, bval]
    refine piV_congr fun k hk => ?_
    rw [interp_pi]
    simp only [natSuccAV, interp_app, interp_bvar, interp_const,
      cons, bval]
    exact piV_congr fun _ _ => by rw [natSuccV_app V hk]
  have d4 : ∀ a1 a2 a3 : V,
      interp V (cons a3 (cons a2 (cons a1 ρ))) natTyAV = (omega : V) := by
    intro _ _ _; simp [natTyAV, interp_const, bval]
  rw [WellDenoted_app]
  refine ⟨?_, h4, ?_⟩
  · rw [WellDenoted_app]
    refine ⟨?_, h3, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨⟨trivial, h1, ?_⟩, h2, ?_⟩
      · exact bconst_app_data V .natRec [u] ρ rfl (by rw [hlv, d1]; exact m1)
          (by rw [hlv, d1]; exact IsTy_piR _ _ _)
      · refine bconst_app_data2 V .natRec [u] ρ rfl
          (by rw [hlv, d1]; exact m1) ?_
          (by rw [d2]; exact IsTy_of_mem_univ (natMotive_apply V m1 natzero_mem))
        rw [d2]; exact m2
    · refine bconst_app_data3 V .natRec [u] ρ rfl
        (by rw [hlv, d1]; exact m1) (by rw [d2]; exact m2) ?_
        (by rw [d3]; exact IsTy_piV)
      rw [d3]; exact m3
  · refine bconst_app_data4 V .natRec [u] ρ rfl
      (by rw [hlv, d1]; exact m1) (by rw [d2]; exact m2)
      (by rw [d3]; exact m3) ?_ (by rw [d4]; exact IsTy_omega)
    rw [d4]; exact m4

/-- The `zero` rule's RHS tower is graded. -/
theorem natZeroRa_wellDenoted (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenoted V ρ (natZeroRa ψ) := by
  have hzty : ∀ M : V, interp V (cons M ρ)
      (Term.app (.bvar 0) (.const .natZero [])) = app M natzero := by
    intro M; simp [interp_app, interp_bvar, interp_const, cons, bval]
  rw [natZeroRa, WellDenoted_lam, natMotiveTy_interp]
  have hMz : ∀ M : V, M ∈ˢ natMotiveSpace V (ψ uN) → IsTy (app M natzero) :=
    fun M hM => IsTy_of_mem_univ (natMotive_apply V hM (natzero_mem (V := V)))
  -- the innermost λ, at a motive and a minor
  have hin : ∀ M z : V, M ∈ˢ natMotiveSpace V (ψ uN) → z ∈ˢ app M natzero →
      WellDenoted V (cons z (cons M ρ)) (.lam (natStepTy) (.bvar 1)) ∧
        interp V (cons z (cons M ρ)) (.lam (natStepTy) (.bvar 1)) ∈ˢ
          piV (natStepSpace V M)
            fun _ => app M natzero := by
    intro M z hM hz
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_lam, natStepTy_interp]
      exact ⟨natStepTy_wellDenoted ψ ρ M z hM, IsTy_piV, fun _ _ => trivial,
        fun _ => app M natzero,
        fun _ _ => by simpa [interp_bvar, cons] using hz,
        fun _ _ => hMz M hM⟩
    · rw [interp_lam, natStepTy_interp]
      exact lamV_mem (fun _ _ => by simpa [interp_bvar, cons] using hz)
        fun _ _ => hMz M hM
  refine ⟨natMotiveTy_wellDenoted ψ ρ, IsTy_piR _ _ _, fun M hM => ?_, ?_⟩
  · have hM' : M ∈ˢ piR (ψ uN + 1) (omega : V) fun _ => univ (ψ uN) := by
      rw [← piV_univ_eq_pos (Nat.succ_ne_zero _) (natzero_mem (V := V)) _ fun _ _ => ⟨_, rfl⟩]
      exact hM
    rw [WellDenoted_lam, hzty]
    refine ⟨⟨trivial, trivial, ψ uN + 1, omega, fun _ => univ (ψ uN),
        by simpa [interp_bvar, cons] using hM',
        by simpa [interp_const, bval]
          using (natzero_mem : (natzero : V) ∈ˢ omega),
        fun h => absurd h (Nat.succ_ne_zero _), fun _ => IsTy_omega⟩,
      hMz M hM, fun z hz => (hin M z hM hz).1, ?_⟩
    exact ⟨_, fun z hz => (hin M z hM hz).2, fun _ _ => IsTy_piV⟩
  · refine ⟨fun M => piV (app M natzero) fun _ =>
        piV (natStepSpace V M)
          fun _ => app M natzero,
      fun M hM => ?_, fun _ _ => IsTy_piV⟩
    rw [interp_lam, hzty]
    exact lamV_mem (fun z hz => (hin M z hM hz).2) fun _ _ => IsTy_piV

set_option maxHeartbeats 1000000 in
/-- The `succ` rule's RHS tower is graded — the extra layer over the
`zero` rule's is the recursive spine, `natRecSpine_wellDenoted`. -/
theorem natSuccRa_wellDenoted (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenoted V ρ (natSuccRa ψ) := by
  have hzty : ∀ M : V, interp V (cons M ρ)
      (Term.app (.bvar 0) (.const .natZero [])) = app M natzero := by
    intro M; simp [interp_app, interp_bvar, interp_const, cons, bval]
  have hMty : ∀ M : V, M ∈ˢ natMotiveSpace V (ψ uN) → ∀ n : V, n ∈ˢ (omega : V) →
      IsTy (app M n) := fun M hM n hn => IsTy_of_mem_univ (natMotive_apply V hM hn)
  -- the fourth λ's body, at a fixed motive/minor/step
  have body : ∀ (M z s : V), M ∈ˢ natMotiveSpace V (ψ uN) →
      z ∈ˢ app M natzero →
      s ∈ˢ (natStepSpace V M) →
      ∀ n : V, n ∈ˢ (omega : V) →
      WellDenoted V (cons n (cons s (cons z (cons M ρ))))
          (.app (.app (.bvar 1) (.bvar 0))
            (.app (.app (.app (.app (.const .natRec [ψ uN]) (.bvar 3))
              (.bvar 2)) (.bvar 1)) (.bvar 0))) ∧
        interp V (cons n (cons s (cons z (cons M ρ))))
            (.app (.app (.bvar 1) (.bvar 0))
              (.app (.app (.app (.app (.const .natRec [ψ uN]) (.bvar 3))
                (.bvar 2)) (.bvar 1)) (.bvar 0)))
          ∈ˢ app M (natsucc n) := by
    intro M z s hM hz hs n hn
    have hsn : app s n ∈ˢ piV (app M n) (fun _ => app M (natsucc n)) :=
      app_mem_piV (B := fun k => piV (app M k) fun _ => app M (natsucc k)) hs hn
    have hrec : app (app (app (app (natRecV V (ψ uN)) M) z) s) n
        ∈ˢ app M n := by
      rw [natRecV_app V hM hz hs hn]
      exact natRecV_mem_fibre V hz hs hn
    have espine : interp V (cons n (cons s (cons z (cons M ρ))))
        (.app (.app (.app (.app (.const .natRec [ψ uN]) (.bvar 3))
          (.bvar 2)) (.bvar 1)) (.bvar 0))
        = app (app (app (app (natRecV V (ψ uN)) M) z) s) n := by
      simp [interp_app, interp_bvar, interp_const, cons, bval,
        ConLeche.Term.lv]
    have eapp : interp V (cons n (cons s (cons z (cons M ρ))))
        (Term.app (.bvar 1) (.bvar 0)) = app s n := by
      simp [interp_app, interp_bvar, cons]
    have hs'' : s ∈ˢ piR (propN omega fun k => piV (app M k) fun _ => app M (natsucc k))
        omega (fun k => piV (app M k) fun _ => app M (natsucc k)) := hs
    have hsn'' : app s n ∈ˢ piR (propN (app M n) fun _ => app M (natsucc n))
        (app M n) (fun _ => app M (natsucc n)) := hsn
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨⟨trivial, trivial, _, omega,
          fun k => piV (app M k) (fun _ => app M (natsucc k)),
          by simpa [interp_bvar, cons] using hs'',
          by simpa [interp_bvar, cons] using hn,
          propN_eq_zero.mp, fun _ => IsTy_omega⟩,
        ?_, ?_⟩
      · refine natRecSpine_wellDenoted (u := ψ uN) _ trivial trivial trivial
          trivial ?_ ?_ ?_ ?_
        · simpa [interp_bvar, cons] using hM
        · simpa [interp_bvar, cons] using hz
        · simpa [interp_bvar, cons] using hs
        · simpa [interp_bvar, cons] using hn
      · exact ⟨_, app M n, fun _ => app M (natsucc n),
          by rw [eapp]; exact hsn'',
          by rw [espine]; exact hrec,
          propN_eq_zero.mp,
          fun _ => hMty M hM n hn⟩
    · rw [interp_app, eapp, espine]
      exact app_mem_piV hsn hrec
  -- the fourth λ, at a motive, a minor and a step
  have hlam4 : ∀ M z s : V, M ∈ˢ natMotiveSpace V (ψ uN) → z ∈ˢ app M natzero →
      s ∈ˢ (natStepSpace V M) →
      WellDenoted V (cons s (cons z (cons M ρ)))
          (.lam (.const .nat [])
            (.app (.app (.bvar 1) (.bvar 0))
              (.app (.app (.app (.app (.const .natRec [ψ uN]) (.bvar 3))
                (.bvar 2)) (.bvar 1)) (.bvar 0)))) ∧
        interp V (cons s (cons z (cons M ρ)))
            (.lam (.const .nat [])
              (.app (.app (.bvar 1) (.bvar 0))
                (.app (.app (.app (.app (.const .natRec [ψ uN]) (.bvar 3))
                  (.bvar 2)) (.bvar 1)) (.bvar 0))))
          ∈ˢ piV omega fun n => app M (natsucc n) := by
    intro M z s hM hz hs
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_lam]
      simp only [interp_const, bval]
      exact ⟨trivial, IsTy_omega, fun n hn => (body M z s hM hz hs n hn).1,
        fun n => app M (natsucc n),
        fun n hn => (body M z s hM hz hs n hn).2,
        fun n hn => hMty M hM _ (natsucc_mem hn)⟩
    · rw [interp_lam]
      simp only [interp_const, bval]
      exact lamV_mem (fun n hn => (body M z s hM hz hs n hn).2)
        fun n hn => hMty M hM _ (natsucc_mem hn)
  -- the third λ, at a motive and a minor
  have hlam3 : ∀ M z : V, M ∈ˢ natMotiveSpace V (ψ uN) → z ∈ˢ app M natzero →
      WellDenoted V (cons z (cons M ρ))
          (.lam (natStepTy) (.lam (.const .nat [])
            (.app (.app (.bvar 1) (.bvar 0))
              (.app (.app (.app (.app (.const .natRec [ψ uN]) (.bvar 3))
                (.bvar 2)) (.bvar 1)) (.bvar 0))))) ∧
        interp V (cons z (cons M ρ))
            (.lam (natStepTy) (.lam (.const .nat [])
              (.app (.app (.bvar 1) (.bvar 0))
                (.app (.app (.app (.app (.const .natRec [ψ uN]) (.bvar 3))
                  (.bvar 2)) (.bvar 1)) (.bvar 0)))))
          ∈ˢ piV (natStepSpace V M)
              fun _ => piV omega fun n => app M (natsucc n) := by
    intro M z hM hz
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_lam, natStepTy_interp]
      exact ⟨natStepTy_wellDenoted ψ ρ M z hM, IsTy_piV,
        fun s hs => (hlam4 M z s hM hz hs).1, _,
        fun s hs => (hlam4 M z s hM hz hs).2, fun _ _ => IsTy_piV⟩
    · rw [interp_lam, natStepTy_interp]
      exact lamV_mem (fun s hs => (hlam4 M z s hM hz hs).2) fun _ _ => IsTy_piV
  rw [natSuccRa, WellDenoted_lam, natMotiveTy_interp]
  refine ⟨natMotiveTy_wellDenoted ψ ρ, IsTy_piR _ _ _, fun M hM => ?_, ?_⟩
  · have hM' : M ∈ˢ piR (ψ uN + 1) (omega : V) fun _ => univ (ψ uN) := by
      rw [← piV_univ_eq_pos (Nat.succ_ne_zero _) (natzero_mem (V := V)) _ fun _ _ => ⟨_, rfl⟩]
      exact hM
    rw [WellDenoted_lam, hzty]
    refine ⟨⟨trivial, trivial, ψ uN + 1, omega, fun _ => univ (ψ uN),
        by simpa [interp_bvar, cons] using hM',
        by simpa [interp_const, bval]
          using (natzero_mem : (natzero : V) ∈ˢ omega),
        fun h => absurd h (Nat.succ_ne_zero _), fun _ => IsTy_omega⟩,
      hMty M hM _ natzero_mem, fun z hz => (hlam3 M z hM hz).1, ?_⟩
    exact ⟨_, fun z hz => (hlam3 M z hM hz).2, fun _ _ => IsTy_piV⟩
  · refine ⟨fun M => piV (app M natzero) fun _ =>
        piV (natStepSpace V M)
          fun _ => piV omega fun n => app M (natsucc n),
      fun M hM => ?_, fun _ _ => IsTy_piV⟩
    rw [interp_lam, hzty]
    exact lamV_mem (fun z hz => (hlam3 M z hM hz).2) fun _ _ => IsTy_piV

/-! ### The two rows

Both rules are `.plain` (ENDGAME F §3), so the `.nested` conjuncts are
`nomatch` at both.  What differs from a single fieldless rule is the
shape of the fired equality — `natrec_zero` at one rule, `natrec_succ` at the other
— and that the `succ` rule's right-hand side mentions the recursor
itself, read through the **fresh** leaf. -/

/-- The recursor's telescope, unpacked into the four memberships
`SetModel/Value.lean`'s laws are stated with. -/
theorem natRecTelescope (ψ : Name → Nat) (ρ : Nat → V)
    {xs : List Term} (hxs : xs.length = 3) (tl rest : Term)
    (hfit : TeleFitPA V ρ
      (.pi (natMotiveTy ψ)
        (.pi (.app (.bvar 0) (.const .natZero []))
          (.pi (natStepTy)
            (.pi (.const .nat [])
              (.app (.bvar 3) (.bvar 0))))))
      (xs ++ [tl]) rest) :
    ∃ M z s : Term, xs = [M, z, s] ∧
      interp V ρ M ∈ˢ natMotiveSpace V (ψ uN) ∧
      interp V ρ z ∈ˢ app (interp V ρ M) natzero ∧
      interp V ρ s ∈ˢ natStepSpace V (interp V ρ M) ∧
      interp V ρ tl ∈ˢ (omega : V) := by
  obtain ⟨M, z, s, rfl⟩ : ∃ a b c, xs = [a, b, c] := by
    match xs, hxs with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  cases hfit with | cons h1 hfit =>
  cases hfit with | cons h2 hfit =>
  cases hfit with | cons h3 hfit =>
  cases hfit with | cons h4 _ =>
  rw [natMotiveTy_interp] at h1
  refine ⟨M, z, s, rfl, h1, ?_, ?_, ?_⟩
  · simpa [Term.inst, Term.liftN_zero, interp_app, interp_bvar,
      interp_const, cons, bval] using h2
  · have heq : (piV (omega : V) fun x =>
          piV (app (interp V ρ M) x)
            fun _ => app (interp V ρ M) (app (natSuccV V) x))
        = natStepSpace V (interp V ρ M) :=
      piV_congr fun n hn => piV_congr fun _ _ => by rw [natSuccV_app V hn]
    rw [← heq]
    simpa [Term.inst, Term.liftN_zero, natStepTy,
      interp_liftN2_inst1, interp_liftN3_inst2, interp_pi,
      interp_app, interp_bvar, interp_const, cons_zero, cons_succ,
      bval] using h3
  · simpa [Term.inst, Term.liftN_zero, interp_const, bval]
      using h4

/-- The `zero` tower's membership in its function space. -/
theorem natZeroRa_mem (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natZeroRa ψ)
      ∈ˢ piV (natMotiveSpace V (ψ uN))
        (fun M => piV (app M natzero)
          (fun _ => piV (natStepSpace V M) (fun _ => app M natzero))) := by
  rw [natZeroRa_interp]
  refine lamV_mem (fun M hM => lamV_mem (fun z hz => lamV_mem (fun _ _ => hz)
    fun _ _ => ?_) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV
  exact IsTy_of_mem_univ (natMotive_apply V hM (natzero_mem (V := V)))

/-- The `succ` tower's membership in its function space. -/
theorem natSuccRa_mem (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natSuccRa ψ)
      ∈ˢ piV (natMotiveSpace V (ψ uN))
        (fun M => piV (app M natzero)
          (fun _ => piV (natStepSpace V M)
            (fun _ => piV omega
              (fun n => app M (natsucc n))))) := by
  rw [natSuccRa_interp]
  refine lamV_mem (fun M hM => lamV_mem (fun z hz =>
    lamV_mem (fun s hs => lamV_mem (fun n hn => ?_) fun n hn =>
      IsTy_of_mem_univ (natMotive_apply V hM (natsucc_mem hn)))
      fun _ _ => IsTy_piV) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV
  have hsn := app_mem_piV (B := fun k => piV (app M k) fun _ => app M (natsucc k)) hs hn
  refine app_mem_piV hsn ?_
  rw [natRecV_app V hM hz hs hn]
  exact natRecV_mem_fibre V hz hs hn

/-- The `zero` rule's transport: three `WellDenoted_app` steps over
`natZeroRa_mem`. -/
theorem natZeroRa_transport (ψ : Name → Nat) (ρ : Nat → V)
    {M z s : Term}
    (hM : interp V ρ M ∈ˢ natMotiveSpace V (ψ uN))
    (hz : interp V ρ z ∈ˢ app (interp V ρ M) natzero)
    (hs : interp V ρ s ∈ˢ natStepSpace V (interp V ρ M))
    (okM : WellDenoted V ρ M) (okz : WellDenoted V ρ z)
    (oks : WellDenoted V ρ s) :
    WellDenoted V ρ (.app (.app (.app (natZeroRa ψ) M) z) s) := by
  have h1 := app_mem_piV (natZeroRa_mem ψ ρ) hM
  have h2 := app_mem_piV h1 hz
  have hMz : IsTy (app (interp V ρ M) natzero) :=
    IsTy_of_mem_univ (natMotive_apply V hM (natzero_mem (V := V)))
  rw [WellDenoted_app]
  refine ⟨?_, oks, slot_of_mem_piV V h2 hs IsTy_piV⟩
  rw [WellDenoted_app]
  refine ⟨?_, okz, slot_of_mem_piV V h1 hz hMz⟩
  rw [WellDenoted_app]
  exact ⟨natZeroRa_wellDenoted ψ ρ, okM,
    slot_of_mem_piV V (natZeroRa_mem ψ ρ) hM (IsTy_piR _ _ _)⟩

/-- The `succ` rule's transport: four steps. -/
theorem natSuccRa_transport (ψ : Name → Nat) (ρ : Nat → V)
    {M z s n : Term}
    (hM : interp V ρ M ∈ˢ natMotiveSpace V (ψ uN))
    (hz : interp V ρ z ∈ˢ app (interp V ρ M) natzero)
    (hs : interp V ρ s ∈ˢ natStepSpace V (interp V ρ M))
    (hn : interp V ρ n ∈ˢ (omega : V))
    (okM : WellDenoted V ρ M) (okz : WellDenoted V ρ z)
    (oks : WellDenoted V ρ s) (okn : WellDenoted V ρ n) :
    WellDenoted V ρ (.app (.app (.app (.app (natSuccRa ψ) M) z) s) n) := by
  have h1 := app_mem_piV (natSuccRa_mem ψ ρ) hM
  have h2 := app_mem_piV h1 hz
  have h3 := app_mem_piV h2 hs
  rw [WellDenoted_app]
  refine ⟨?_, okn, slot_of_mem_piV V h3 hn IsTy_omega⟩
  rw [WellDenoted_app]
  refine ⟨?_, oks, slot_of_mem_piV V h2 hs IsTy_piV⟩
  rw [WellDenoted_app]
  refine ⟨?_, okz, slot_of_mem_piV V h1 hz
    (IsTy_of_mem_univ (natMotive_apply V hM (natzero_mem (V := V))))⟩
  rw [WellDenoted_app]
  exact ⟨natSuccRa_wellDenoted ψ ρ, okM,
    slot_of_mem_piV V (natSuccRa_mem ψ ρ) hM (IsTy_piR _ _ _)⟩

/-- Both rows share this: the recursor's instantiated type reading,
folded back into the two named domains. -/
theorem natRecTyRead (m₂ : EnvModel V ⟨natRecA :: env.consts, env.tables⟩)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hac : m₂.acval = acvalWith m.acval natRecA.name A)
    (φ : Name → Nat) (us : List Level) {ψ : Name → Nat}
    (hψ : ψ = Level.substFn φ natRecA.toConstantVal.levelParams us) :
    denote m₂.acval ⟨natRecA :: env.consts, env.tables⟩ φ 0
        (natRecA.toConstantVal.type.instantiateLevelParams
          natRecA.toConstantVal.levelParams us)
      = some (.pi (natMotiveTy ψ)
          (.pi (.app (.bvar 0) (.const .natZero []))
            (.pi (natStepTy)
              (.pi (.const .nat [])
                (.app (.bvar 3) (.bvar 0)))))) := by
  rw [denote_instLevels m₂.acval_params φ, hac,
    denote_natRecA_type (m := m) _ hN hZ hS, ← hψ]
  rfl

/-- The major of a `Nat.rec` spine fitting the recursor's instantiated
type reads in `ω`, which holds no point. -/
theorem natRecMajor_ne_pt (m₂ : EnvModel V ⟨natRecA :: env.consts, env.tables⟩)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hac : m₂.acval = acvalWith m.acval natRecA.name A)
    (φ : Name → Nat) (us : List Level) {TVa : Term}
    (hTVa : denote m₂.acval ⟨natRecA :: env.consts, env.tables⟩ φ 0
        (natRecA.toConstantVal.type.instantiateLevelParams
          natRecA.toConstantVal.levelParams us) = some TVa)
    (ρ : Nat → V) {xs : List Term} {a restR : Term}
    (hxs : xs.length = 3) (hfit : TeleFitPA V ρ TVa (xs ++ [a]) restR) :
    interp V ρ a ≠ pt := by
  obtain rfl : TVa = _ := (Option.some.inj
    ((natRecTyRead (m := m) m₂ hN hZ hS hac φ us rfl).symm.trans
      hTVa)).symm
  obtain ⟨-, -, -, -, -, -, -, ha⟩ := natRecTelescope _ ρ hxs a restR hfit
  intro h
  rw [h] at ha
  exact pt_not_mem_omega ha

/-- **`Nat.rec`'s ι facts**, either rule: not K; the major's
domain `ω` holds no point, so (S) and (P) hold outright; the
constructors have no level parameters, so (T) is the fired application
itself; no indices, so (U) is the trivial index pin. -/
theorem natRecExtra (m₂ : EnvModel V ⟨natRecA :: env.consts, env.tables⟩)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hac : m₂.acval = acvalWith m.acval natRecA.name A)
    (φ : Name → Nat) (rl : RecRule) (hk : rl.k = false)
    (harity : ∀ (cvj : ConstantVal) (cnP cnF : Nat),
      (⟨natRecA :: env.consts, env.tables⟩ : Env).find? rl.ctor
        = some (.ctorInfo cvj cnP cnF) →
      (cvj.type.stripPis (rl.ctorParams + rl.nfields)).isSome = true)
    (hlps : ∀ (cvj : ConstantVal) (cnP cnF : Nat),
      (⟨natRecA :: env.consts, env.tables⟩ : Env).find? rl.ctor
        = some (.ctorInfo cvj cnP cnF) → cvj.levelParams = []) :
    RecRuleExtra m₂ φ natRecA.name natRecA.toConstantVal 3 3 rl := by
  intro us _ TVa hTVa
  refine ⟨fun h => by simp [hk] at h, fun cvj cnP cnF hfj =>
    ⟨harity cvj cnP cnF hfj, fun _ => ⟨?_, ?_, fun usj _ _ TVja _ => ⟨?_, ?_⟩⟩⟩⟩
  · intro _ ρ xs a restR hxs hfit
    exact natRecMajor_ne_pt (m := m) m₂ hN hZ hS hac φ us hTVa ρ hxs hfit
  · -- no level parameters: the fired application is at the comparand levels
    intro _ usj husj TVja hTVja ρ xs ys restR restC _ _ _ hfitC _ hyWD _
    have hl := hlps cvj cnP cnF hfj
    refine ⟨usj, ys, TVja, restC, husj, ?_, hTVja, rfl, rfl, hyWD, hfitC, rfl⟩
    rw [hl]
    rfl
  · intro ρ xs a restR hxs hfit ha
    exact absurd ha
      (natRecMajor_ne_pt (m := m) m₂ hN hZ hS hac φ us hTVa ρ hxs hfit)
  · intro ρ xs ys restR restC _ _ _ _ _ _ _ _ _ _
    exact ⟨restC, [], rfl, Or.inl rfl, fun i hi => absurd hi (by omega)⟩

/-- `Nat.rec`'s `zero` rule's ι facts. -/
theorem natRecZeroExtra (m₂ : EnvModel V ⟨natRecA :: env.consts, env.tables⟩)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hac : m₂.acval = acvalWith m.acval natRecA.name A)
    (φ : Name → Nat) :
    RecRuleExtra m₂ φ natRecA.name natRecA.toConstantVal 3 3
      natRecZeroRule :=
  natRecExtra (m := m) m₂ hN hZ hS hac φ _ rfl
    (fun _ _ _ _ => rfl) (by
      intro cvj cnP cnF hfj
      have hZ' : (⟨natRecA :: env.consts, env.tables⟩ : Env).find? natZeroName
          = some natZeroA := by
        rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hZ
      rw [show RecRule.ctor natRecZeroRule = natZeroName from rfl,
        hZ'] at hfj
      injection Option.some.inj hfj with a1 _ _
      rw [← a1])

/-- `Nat.rec`'s `succ` rule's ι facts. -/
theorem natRecSuccExtra (m₂ : EnvModel V ⟨natRecA :: env.consts, env.tables⟩)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hac : m₂.acval = acvalWith m.acval natRecA.name A)
    (φ : Name → Nat) :
    RecRuleExtra m₂ φ natRecA.name natRecA.toConstantVal 3 3
      natRecSuccRule := by
  have hS' : (⟨natRecA :: env.consts, env.tables⟩ : Env).find? natSuccName
      = some natSuccA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hS
  refine natRecExtra (m := m) m₂ hN hZ hS hac φ _ rfl ?_ ?_
  · intro cvj cnP cnF hfj
    rw [show RecRule.ctor natRecSuccRule = natSuccName from rfl,
      hS'] at hfj
    injection Option.some.inj hfj with a1 _ _
    have hcvj : cvj = natSuccA.toConstantVal := a1.symm
    subst hcvj
    rfl
  · intro cvj cnP cnF hfj
    rw [show RecRule.ctor natRecSuccRule = natSuccName from rfl,
      hS'] at hfj
    injection Option.some.inj hfj with a1 _ _
    rw [← a1]

/-- **`Nat.rec`'s `zero` row.** -/
theorem natRecZeroLaw {m : EnvModel V env}
    (m₂ : EnvModel V ⟨natRecA :: env.consts, env.tables⟩)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hac : m₂.acval = acvalWith m.acval natRecA.name
      (fun ψ => Term.const .natRec [ψ uN]))
    (φ : Name → Nat) :
    RecRuleLaw m₂ φ natRecA.name natRecA.toConstantVal 3 3
      natRecZeroRule := by
  refine ⟨Nat.le_refl 3, fun us hus => ?_,
    natRecZeroExtra (m := m) m₂ hN hZ hS hac φ⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ natRecA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  refine ⟨natZeroRa ψ, ?_, natZeroRa_wellDenoted ψ, ?_, ?_⟩
  · rw [denote_instLevels m₂.acval_params φ, hac, hψ,
      denote_natRec_zeroRhs (m := m) _ hN hZ hS]
  · intro _ _ h; exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev _ hpin hTVa hTVja hfitR hfitC
  obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hys
  obtain rfl : TVa = _ := (Option.some.inj
    ((natRecTyRead (m := m) m₂ hN hZ hS hac φ us hψ).symm.trans
      hTVa)).symm
  obtain ⟨M, z, s, rfl, hM, hz, hs, -⟩ :=
    natRecTelescope ψ ρ hxs _ restR hfitR
  have hctorL : m₂.acval (RecRule.ctor natRecZeroRule)
      (Level.substFn φ cvj.levelParams usj)
      = Term.const .natZero [] := by
    rw [show RecRule.ctor natRecZeroRule = natZeroName from rfl, hac,
      acvalWith_ne (by decide)]
    refine EnvModel.acval_pinned m hZ (by decide) ?_
    simp +decide [ConLeche.Verify.pinnedStructT]
  have hrecL : m₂.acval natRecA.name
      (Level.substFn φ natRecA.toConstantVal.levelParams us)
      = Term.const .natRec [ψ uN] := by
    rw [hac, acvalWith_self, hψ]
  refine ⟨?_, ?_⟩
  · simp only [show natRecZeroRule.ctorParams = 0 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      List.append_nil, Term.mkAppN_cons, Term.mkAppN_nil, hrecL,
      hctorL, interp_app, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero]
    rw [natRecV_app V hM hz hs (natzero_mem (V := V)), natrec_zero,
      natZeroRa_interp, app_lamV hM, app_lamV hz, app_lamV hs]
  · intro hxsA _
    simp only [List.take]
    exact natZeroRa_transport ψ ρ hM hz hs
      (hxsA M (by simp)) (hxsA z (by simp)) (hxsA s (by simp))

/-- **`Nat.rec`'s `succ` row** — the RHS mentions the recursor, read
through the *fresh* leaf. -/
theorem natRecSuccLaw {m : EnvModel V env}
    (m₂ : EnvModel V ⟨natRecA :: env.consts, env.tables⟩)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hac : m₂.acval = acvalWith m.acval natRecA.name
      (fun ψ => Term.const .natRec [ψ uN]))
    (φ : Name → Nat) :
    RecRuleLaw m₂ φ natRecA.name natRecA.toConstantVal 3 3
      natRecSuccRule := by
  refine ⟨Nat.le_refl 3, fun us hus => ?_,
    natRecSuccExtra (m := m) m₂ hN hZ hS hac φ⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ natRecA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  refine ⟨natSuccRa ψ, ?_, natSuccRa_wellDenoted ψ, ?_, ?_⟩
  · rw [denote_instLevels m₂.acval_params φ, hac, hψ,
      denote_natRec_succRhs (m := m) _ hN hZ hS]
  · intro _ _ h; exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev _ hpin hTVa hTVja hfitR hfitC
  obtain ⟨n, rfl⟩ : ∃ a, ys = [a] := by
    match ys, hys with
    | [a], _ => exact ⟨a, rfl⟩
  obtain rfl : TVa = _ := (Option.some.inj
    ((natRecTyRead (m := m) m₂ hN hZ hS hac φ us hψ).symm.trans
      hTVa)).symm
  obtain ⟨M, z, s, rfl, hM, hz, hs, -⟩ :=
    natRecTelescope ψ ρ hxs _ restR hfitR
  have hctorL : m₂.acval (RecRule.ctor natRecSuccRule)
      (Level.substFn φ cvj.levelParams usj)
      = Term.const .natSucc [] := by
    rw [show RecRule.ctor natRecSuccRule = natSuccName from rfl, hac,
      acvalWith_ne (by decide)]
    refine EnvModel.acval_pinned m hS (by decide) ?_
    simp +decide [ConLeche.Verify.pinnedStructT]
  have hrecL : m₂.acval natRecA.name
      (Level.substFn φ natRecA.toConstantVal.levelParams us)
      = Term.const .natRec [ψ uN] := by
    rw [hac, acvalWith_self, hψ]
  -- `n`'s membership comes from the *constructor's* telescope
  have hcvj : cvj = natSuccA.toConstantVal := by
    have hS' : (⟨natRecA :: env.consts, env.tables⟩ : Env).find? natSuccName
        = some natSuccA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hS
    rw [show RecRule.ctor natRecSuccRule = natSuccName from rfl,
      hS'] at hfj
    injection Option.some.inj hfj with a1 _ _
    exact a1.symm
  subst hcvj
  have hTVja' : TVja = .pi (.const .nat []) (.const .nat []) := by
    rw [denote_instLevels m₂.acval_params φ, hac,
      denote_natSuccTy (m := m) _ (by decide) hN] at hTVja
    exact (Option.some.inj hTVja).symm
  subst hTVja'
  cases hfitC with | cons hn _ =>
  have hn' : interp V ρ n ∈ˢ (omega : V) := by
    simpa [interp_const, bval] using hn
  refine ⟨?_, ?_⟩
  · simp only [List.take, List.drop, List.cons_append, List.nil_append,
      Term.mkAppN_cons, Term.mkAppN_nil, hrecL,
      hctorL, interp_app, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero, show natRecSuccRule.ctorParams = 0 from rfl]
    rw [natSuccV_app V hn',
      natRecV_app V hM hz hs (natsucc_mem hn'), natrec_succ _ _ hn',
      natSuccRa_interp]
    rw [app_lamV hM, app_lamV hz, app_lamV hs, app_lamV hn',
      natRecV_app V hM hz hs hn']
  · intro hxsA hysA
    simp only [List.take, List.drop,
      show natRecSuccRule.ctorParams = 0 from rfl]
    exact natSuccRa_transport ψ ρ hM hz hs hn'
      (hxsA M (by simp)) (hxsA z (by simp)) (hxsA s (by simp))
      (hysA n (by simp))

/-- **`Nat.rec`, installed at the P tier.** -/
theorem extendNatRec (mp : EnvModelM V μ env)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hfresh : env.find? natRecA.name = none)
    (hwf : EnvWF ⟨natRecA :: env.consts, env.tables⟩) {ex : List Name} :
    CoverTo mp ex ⟨natRecA :: env.consts, env.tables⟩ ex := by
  have hty := fun ψ =>
    denote_natRecA_type (m := mp.base2)
      (A := fun ψ => Term.const .natRec [ψ uN]) ψ hN hZ hS
  refine coverTo_cons hfresh (fun _ _ h => nomatch h) (declStep_preserves_of_basis_rec_cons mp
    (A := fun ψ => Term.const .natRec [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT natRecA.name ψ
          = some (Term.const .natRec [ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp])
      (fun _ _ _ _ heq r hr => by
        injection heq with _ _ _ h4
        rw [← h4] at hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨⟨_, _, _, hZ⟩, fun hb => Bool.noConfusion hb,
            fun hb => Bool.noConfusion hb⟩
        rcases List.mem_cons.mp hr' with rfl | hr''
        · exact ⟨⟨_, _, _, hS⟩, fun hb => Bool.noConfusion hb,
            fun hb => Bool.noConfusion hb⟩
        · exact nomatch hr''))
    ?_
    (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [natRecA_reading_eq]
    exact WellDenotedTy_bconst_type V .natRec [ψ uN] ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [natRecA_reading_eq]
    exact bval_mem_type V .natRec [ψ uN] ρ
  · intro m₂ hac φ
    refine recRules_cons_rec mp hfresh natRecA_eq m₂ hac φ ?_
    intro rl hrl
    rcases List.mem_cons.mp hrl with rfl | hr'
    · exact natRecZeroLaw (m := mp.base2) m₂ hN hZ hS hac φ
    · rcases List.mem_cons.mp hr' with rfl | hr''
      · exact natRecSuccLaw (m := mp.base2) m₂ hN hZ hS hac φ
      · exact nomatch hr''

/-- **The `Nat` block, installed at the P tier.**  `BasisStepPB`'s
`natK` branch. -/
theorem declBasisPB_natK {env₁ : Env} (mp : EnvModelM V μ env)
    (h : ConLeche.Semantics.BasisInstallRun env
      ConLeche.BasisKind.natK.declsA env₁) :
    CoverStep mp env₁ := by
  rw [show ConLeche.BasisKind.natK.declsA
    = [natA, natZeroA, natSuccA, natRecA] from rfl] at h
  obtain ⟨h1, h2, h3, h4, hnil⟩ := h
  subst hnil
  have hf1 : env.find? natA.name = none :=
    Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨natA :: env.consts, env.tables⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
  have hf2 : (⟨natA :: env.consts, env.tables⟩ : Env).find? natZeroA.name = none :=
    Option.isNone_iff_eq_none.mp h2
  refine (extendNat mp hf1
    (by simp [ConLeche.natLitSupported, ConLeche.natZeroOk,
      show (⟨natA :: env.consts, env.tables⟩ : Env).find? natZeroName = none
        from hf2]) hwf1).trans fun mp1 => ?_
  have hN1 : (⟨natA :: env.consts, env.tables⟩ : Env).find? natName
      = some natA := by
    rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl
  have hwf2 : EnvWF ⟨natZeroA :: natA :: env.consts, env.tables⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ natZeroA.toConstantVal.type = true
    have hf : (⟨natZeroA :: natA :: env.consts, env.tables⟩ : Env).find? natName
        = some natA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN1
    rw [show natZeroA.toConstantVal.type = Expr.const natName []
      from rfl]
    simp [Expr.constsResolve, hf]
  have hf3 : (⟨natZeroA :: natA :: env.consts, env.tables⟩ : Env).find?
      natSuccA.name = none := Option.isNone_iff_eq_none.mp h3
  refine (extendNatZero mp1 hN1 hf2
    (by simp [ConLeche.natLitSupported, ConLeche.natSuccOk,
      show (⟨natZeroA :: natA :: env.consts, env.tables⟩ : Env).find? natSuccName
        = none from hf3]) hwf2 List.mem_cons_self).trans fun mp2 => ?_
  have hN2 : (⟨natZeroA :: natA :: env.consts, env.tables⟩ : Env).find? natName
      = some natA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN1
  have hZ2 : (⟨natZeroA :: natA :: env.consts, env.tables⟩ : Env).find? natZeroName
      = some natZeroA := by
    rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl
  have hwf3 : EnvWF ⟨natSuccA :: natZeroA :: natA :: env.consts, env.tables⟩ := by
    refine EnvWF.cons hwf2 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ natSuccA.toConstantVal.type = true
    have hf : (⟨natSuccA :: natZeroA :: natA :: env.consts, env.tables⟩
        : Env).find? natName = some natA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN2
    rw [show natSuccA.toConstantVal.type
      = Expr.forallE (.const natName [])
        (.const natName []) from rfl]
    simp [Expr.constsResolve, hf]
  refine (extendNatSucc mp2 hN2 hZ2 hf3 hwf3).trans fun mp3 => ?_
  have hN3 : (⟨natSuccA :: natZeroA :: natA :: env.consts, env.tables⟩
      : Env).find? natName = some natA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN2
  have hZ3 : (⟨natSuccA :: natZeroA :: natA :: env.consts, env.tables⟩
      : Env).find? natZeroName = some natZeroA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hZ2
  have hS3 : (⟨natSuccA :: natZeroA :: natA :: env.consts, env.tables⟩
      : Env).find? natSuccName = some natSuccA := by
    rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl
  have hf4 : (⟨natSuccA :: natZeroA :: natA :: env.consts, env.tables⟩
      : Env).find? natRecA.name = none :=
    Option.isNone_iff_eq_none.mp h4
  have hwf4 : EnvWF ⟨natRecA :: natSuccA :: natZeroA :: natA
      :: env.consts, env.tables⟩ := by
    have hfN : (⟨natRecA :: natSuccA :: natZeroA :: natA
        :: env.consts, env.tables⟩ : Env).find? natName = some natA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN3
    have hfZ : (⟨natRecA :: natSuccA :: natZeroA :: natA
        :: env.consts, env.tables⟩ : Env).find? natZeroName = some natZeroA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hZ3
    have hfS : (⟨natRecA :: natSuccA :: natZeroA :: natA
        :: env.consts, env.tables⟩ : Env).find? natSuccName = some natSuccA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hS3
    refine EnvWF.cons hwf3 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), ?_,
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    · show Expr.constsResolve _ natRecA.toConstantVal.type = true
      rw [show natRecA.toConstantVal.type
          = Expr.forallE
              (Expr.forallE
                (.const natName []) (.sort (.param uN)))
              (Expr.forallE
                (.app (.bvar 0) (.const natZeroName []))
                (Expr.forallE
                  (Expr.forallE
                    (.const natName [])
                    (Expr.forallE
                      (.app (.bvar 2) (.bvar 0))
                      (.app (.bvar 3)
                        (.app (.const natSuccName []) (.bvar 1)))))
                  (Expr.forallE
                    (.const natName []) (.app (.bvar 3) (.bvar 0))))) from rfl]
      simp only [Expr.constsResolve, hfN, hfZ, hfS, Option.isSome_some,
        Bool.and_self]
    · intro cv mI rP rules heq
      injection heq with h1' h2' h3' h4'
      subst h4'
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · refine ⟨rfl, ?_, ?_, rfl, fun lvls pins heqf => nomatch heqf⟩
        · subst h1'; rfl
        · show Expr.constsResolve _ natRecZeroRule.rhs = true
          rw [show natRecZeroRule.rhs = _ from rfl]
          simp only [natRecZeroRule, Expr.constsResolve, hfN, hfZ, hfS,
            Option.isSome_some, Bool.and_self]
      · rcases List.mem_cons.mp hr' with rfl | hr''
        · refine ⟨rfl, ?_, ?_, rfl, fun lvls pins heqf => nomatch heqf⟩
          · subst h1'; rfl
          · show Expr.constsResolve _ natRecSuccRule.rhs = true
            have hfR : (⟨natRecA :: natSuccA :: natZeroA :: natA
                :: env.consts, env.tables⟩ : Env).find? (natName.str "rec")
                = some natRecA := by
              rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl
            simp only [natRecSuccRule, Expr.constsResolve, hfN, hfZ,
              hfS, hfR, Option.isSome_some, Bool.and_self]
        · exact nomatch hr''
  exact extendNatRec mp3 hN3 hZ3 hS3 hf4  hwf4

end Nat

end ConLeche.Model
