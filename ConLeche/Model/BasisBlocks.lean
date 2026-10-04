module

public import ConLeche.Model.Levels
public import ConLeche.Semantics.BasisRules
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen
import ConLeche.Model.Annot.BitInst

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

* `denoteMeta_pinned_const` — a *leveled* pinned leaf's reading;
* `denoteMeta_instLevels` (`Model/Levels.lean`) — so that a recursor
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
open ConLeche.Semantics (AnnotTerm)
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
`acval_basis_pinned`. -/
theorem denoteMeta_pinned_const {m : EnvModel V env}
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    {n : Name} {ci : ConstantInfo} {ψ : Name → Nat} {ls : List Level}
    (hne : ¬ c₀.name = n)
    (hf : env.find? n = some ci)
    (hres : ConLeche.reservedBasisNames.contains n = true)
    (hlen : ls.length = ci.toConstantVal.levelParams.length)
    {c : ConLeche.Term.BConst} {us : List Nat}
    (hpd : ConLeche.Verify.pinnedStructT n
      (Level.substFn ψ ci.toConstantVal.levelParams ls)
        = some (Term.const c us)) (d : Nat) :
    denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const n ls) = some (AnnotTerm.const c us) := by
  have hf' : (⟨c₀ :: env.consts⟩ : Env).find? n = some ci := by
    rw [ConLeche.Env.find?_cons, ite_eq_right hne]; exact hf
  rw [denoteMeta_const hf' hlen, acvalWith_ne (fun h => hne h.symm),
    acval_basis_pinned (m := m) hf hres hpd]

/-! ### Lift-then-instantiate absorption

`TeleFitPA` peels a `.pi` by `B.inst a`, so a telescope domain that
mentions an *earlier* argument arrives as that argument's reading
lifted past the intervening binders and then instantiated.  The two
instances the basis recursors' step spaces need. -/

/-- The general absorption: lifting past `k + 1` binders and
instantiating at `k` shifts the environment down by `k`. -/
theorem interp_liftN_succ_inst (e a : AnnotTerm) (k : Nat)
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

theorem interp_liftN2_inst1 (e a : AnnotTerm) (x : V) (ρ : Nat → V) :
    interp V (cons x ρ) ((e.liftN 2 0).inst a 1) = interp V ρ e := by
  rw [interp_liftN_succ_inst (k := 1)]
  rfl

theorem interp_liftN3_inst2 (e a : AnnotTerm) (x y : V) (ρ : Nat → V) :
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

variable {m : EnvModel V env} {A : (Name → Nat) → AnnotTerm}

/-- `Nat`'s type reading: `Sort 1`, `BConst.typeAV .nat []` on the
nose. -/
theorem denoteMeta_natA_type
    {acval : Name → (Name → Nat) → AnnotTerm} (ψ : Name → Nat) :
    denoteMeta acval ⟨natA :: env.consts⟩ ψ 0 natA.toConstantVal.type
      = some (BConst.typeAV .nat []) := by
  rw [show natA.toConstantVal.type = Expr.sort (.succ .zero) from rfl,
    denoteMeta_sort]
  rfl

/-- The pinned `Nat` leaf at an extension. -/
theorem denoteMeta_natLeaf {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = natName)
    (hN : env.find? natName = some natA) (d : Nat) :
    denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const natName []) = some (AnnotTerm.const .nat []) := by
  refine denoteMeta_pinned_const (m := m) hne hN (by decide) (by rfl) ?_ d
  simp +decide [ConLeche.Verify.pinnedStructT]

/-- `Nat.zero`'s type reading. -/
theorem denoteMeta_natZeroA_type (ψ : Name → Nat)
    (hN : env.find? natName = some natA) :
    denoteMeta (acvalWith m.acval natZeroA.name A)
        ⟨natZeroA :: env.consts⟩ ψ 0 natZeroA.toConstantVal.type
      = some (BConst.typeAV .natZero []) := by
  rw [show natZeroA.toConstantVal.type = Expr.const natName [] from rfl]
  exact denoteMeta_natLeaf (m := m) (A := A) ψ (by decide) hN 0

/-- `Nat.succ`'s type reading — one binder, pinned `.never`, so the
numeral is `1` on both sides.  Stated at *any* extension whose cons is
not `Nat`, because the `Nat.rec` row reads it too (its rule's
constructor is `Nat.succ`). -/
theorem denoteMeta_natSuccTy {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = natName)
    (hN : env.find? natName = some natA) :
    denoteMeta (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ 0
        natSuccA.toConstantVal.type
      = some (.pi 0 (pwBit ψ .never) (.const .nat [])
          (.const .nat [])) := by
  have hNc := fun d => denoteMeta_natLeaf (m := m) (A := A) (c₀ := c₀)
    ψ hne hN d
  rw [show natSuccA.toConstantVal.type
      = Expr.forallE (.const natName [])
          (.const natName []) { pw := .never } from rfl]
  simp [denoteMeta_forallE, Expr.instantiate1, hNc]

theorem denoteMeta_natSuccA_type (ψ : Name → Nat)
    (hN : env.find? natName = some natA) :
    denoteMeta (acvalWith m.acval natSuccA.name A)
        ⟨natSuccA :: env.consts⟩ ψ 0 natSuccA.toConstantVal.type
      = some (.pi 0 (pwBit ψ .never) (.const .nat [])
          (.const .nat [])) :=
  denoteMeta_natSuccTy (m := m) (A := A) ψ (by decide) hN

theorem bitAgree_natSuccA (ψ : Name → Nat) :
    AnnotTerm.BitAgree
      (.pi 0 (pwBit ψ .never) (.const .nat []) (.const .nat []))
      (BConst.typeAV .natSucc []) := by
  refine .pi ?_ (.const _ _) (.const _ _)
  rw [pwBit_never]

/-- The three pinned `Nat` leaves at the `Nat.rec` extension. -/
theorem denoteMeta_natRec_leaves (ψ : Name → Nat)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    (∀ d : Nat, denoteMeta (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts⟩ ψ d (.const natName [])
        = some (AnnotTerm.const .nat [])) ∧
    (∀ d : Nat, denoteMeta (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts⟩ ψ d (.const natZeroName [])
        = some (AnnotTerm.const .natZero [])) ∧
    (∀ d : Nat, denoteMeta (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts⟩ ψ d (.const natSuccName [])
        = some (AnnotTerm.const .natSucc [])) := by
  refine ⟨fun d => denoteMeta_natLeaf (m := m) (A := A) ψ (by decide) hN d,
    fun d => ?_, fun d => ?_⟩
  · refine denoteMeta_pinned_const (m := m) (by decide) hZ (by decide)
      (by rfl) ?_ d
    simp +decide [ConLeche.Verify.pinnedStructT]
  · refine denoteMeta_pinned_const (m := m) (by decide) hS (by decide)
      (by rfl) ?_ d
    simp +decide [ConLeche.Verify.pinnedStructT]

/-- **`Nat.rec`'s type reading.**  Seven binders; six carry
`.ifAllZero [u]` and the motive's domain carries `.never`. -/
theorem denoteMeta_natRecA_type (ψ : Name → Nat)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denoteMeta (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts⟩ ψ 0 natRecA.toConstantVal.type
      = some (.pi 0 (pwBit ψ (.ifAllZero [uN]))
          (.pi 0 (pwBit ψ .never) (.const .nat []) (.sort (ψ uN)))
          (.pi 0 (pwBit ψ (.ifAllZero [uN]))
            (.app (.bvar 0) (.const .natZero []))
            (.pi 0 (pwBit ψ (.ifAllZero [uN]))
              (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
                (.pi 0 (pwBit ψ (.ifAllZero [uN]))
                  (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 3)
                    (.app (.const .natSucc []) (.bvar 1)))))
              (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
                (.app (.bvar 3) (.bvar 0)))))) := by
  obtain ⟨hNc, hZc, hSc⟩ :=
    denoteMeta_natRec_leaves (m := m) (A := A) ψ hN hZ hS
  rw [show natRecA.toConstantVal.type
      = Expr.forallE
          (Expr.forallE (.const natName [])
            (.sort (.param uN)) { pw := .never })
          (Expr.forallE
            (.app (.bvar 0) (.const natZeroName []))
            (Expr.forallE
              (Expr.forallE (.const natName [])
                (Expr.forallE
                  (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 3)
                    (.app (.const natSuccName []) (.bvar 1)))
                  { pw := .ifAllZero [uN] })
                { pw := .ifAllZero [uN] })
              (Expr.forallE (.const natName [])
                (.app (.bvar 3) (.bvar 0))
                { pw := .ifAllZero [uN] })
              { pw := .ifAllZero [uN] })
            { pw := .ifAllZero [uN] })
          { pw := .ifAllZero [uN] } from rfl]
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
    Expr.instantiate1, hNc, hZc, hSc, Level.eval]

theorem bitAgree_natRecA (ψ : Name → Nat) :
    AnnotTerm.BitAgree
      (.pi 0 (pwBit ψ (.ifAllZero [uN]))
        (.pi 0 (pwBit ψ .never) (.const .nat []) (.sort (ψ uN)))
        (.pi 0 (pwBit ψ (.ifAllZero [uN]))
          (.app (.bvar 0) (.const .natZero []))
          (.pi 0 (pwBit ψ (.ifAllZero [uN]))
            (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
              (.pi 0 (pwBit ψ (.ifAllZero [uN]))
                (.app (.bvar 2) (.bvar 0))
                (.app (.bvar 3)
                  (.app (.const .natSucc []) (.bvar 1)))))
            (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
              (.app (.bvar 3) (.bvar 0))))))
      (BConst.typeAV .natRec [ψ uN]) := by
  have hz : pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0 ↔ ψ uN = 0 :=
    pwBit_ifAllZero_single ψ uN
  refine .pi hz (.pi ?_ (.const _ _) (.sort _))
    (.pi hz (.app (.bvar 0) (.const _ _))
      (.pi hz
        (.pi hz (.const _ _)
          (.pi hz (.app (.bvar 2) (.bvar 0))
            (.app (.bvar 3) (.app (.const _ _) (.bvar 1)))))
        (.pi hz (.const _ _) (.app (.bvar 3) (.bvar 0)))))
  rw [pwBit_never]
  simp

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
    (hguard : ConLeche.natLitSupported ⟨natA :: env.consts⟩ = false)
    (hwf : EnvWF ⟨natA :: env.consts⟩) :
    CoverTo mp [] ⟨natA :: env.consts⟩ [natName] := by
  -- the pinned block's lfp clause is recorded at its last constructor's
  -- cons (`extendNatSucc`: the clause's `ctor` reads the constructors' leaves)
  refine coverTo_pend hfresh (declStep_preserves_of_basis_cons_gen mp
    (A := fun _ => AnnotTerm.const .nat []) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT natA.name ψ
          = some (Term.const .nat []) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, denoteMeta_natA_type ψ⟩) ?_ ?_ ?_ ?_)
  · intro ψ ta h ρ
    rw [denoteMeta_natA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact WellDenotedV_bconst_type V .nat [] ρ
  · intro ψ ta h ρ
    rw [denoteMeta_natA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval_mem_type V .nat [] ρ
  · intro _ _ _ hg
    rw [hguard] at hg
    exact nomatch hg
  · exact fun m₂ hac φ => recRules_cons_fresh mp (c₀ := natA) hfresh
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h) m₂ hac φ

/-- **`Nat.zero`, installed at the P tier.** -/
theorem extendNatZero (mp : EnvModelM V μ env)
    (hN : env.find? natName = some natA)
    (hfresh : env.find? natZeroName = none)
    (hguard : ConLeche.natLitSupported ⟨natZeroA :: env.consts⟩ = false)
    (hwf : EnvWF ⟨natZeroA :: env.consts⟩) {ex : List Name} (hNex : natName ∈ ex) :
    CoverTo mp ex ⟨natZeroA :: env.consts⟩ ex := by
  have hty := fun ψ =>
    denoteMeta_natZeroA_type (m := mp.base2)
      (A := fun _ => AnnotTerm.const .natZero []) ψ hN
  refine coverTo_cons hfresh (fun _ _ h => nomatch h)
    (hhead := hhead_ctor (c₀ := natZeroA) rfl rfl rfl (Or.inl hNex))
    (declStep_preserves_of_basis_cons_gen mp
    (A := fun _ => AnnotTerm.const .natZero []) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT natZeroA.name ψ
          = some (Term.const .natZero []) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_ ?_)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact WellDenotedV_bconst_type V .natZero [] ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval_mem_type V .natZero [] ρ
  · intro _ _ _ hg
    rw [hguard] at hg
    exact nomatch hg
  · exact fun m₂ hac φ => recRules_cons_fresh mp (c₀ := natZeroA)
      (hntc := fun _ h => nomatch h)
      hfresh (fun _ _ _ _ h => nomatch h) m₂ hac φ

/-- **`Nat.succ`, installed at the P tier** — the cons where the
literal guard becomes true, so `nat_heads` is bespoke here and nowhere
else.  Its content is `natzero_mem` and `natSuccV_mem`. -/
theorem extendNatSucc (mp : EnvModelM V μ env)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hfresh : env.find? natSuccName = none)
    (hwf : EnvWF ⟨natSuccA :: env.consts⟩) :
    CoverTo mp [natName] ⟨natSuccA :: env.consts⟩ [] := by
  have hty := fun ψ =>
    denoteMeta_natSuccA_type (m := mp.base2)
      (A := fun _ => AnnotTerm.const .natSucc []) ψ hN
  -- the pinned block's lfp clause, recorded at its last constructor's cons
  -- (the constructors' leaves are read by `ctor`)
  have hNl0 : ∀ ψ : Name → Nat, mp.base2.acval natName ψ = AnnotTerm.const .nat [] :=
    fun ψ => acval_basis_pinned (m := mp.base2) hN (by decide) rfl
  have hZl0 : ∀ ψ : Name → Nat, mp.base2.acval natZeroName ψ = AnnotTerm.const .natZero [] :=
    fun ψ => acval_basis_pinned (m := mp.base2) hZ (by decide) rfl
  refine coverTo_addLfp (D := natLfp natName natZeroName natSuccName)
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
            show (⟨natSuccA :: env.consts⟩ : ConLeche.Env).find? natZeroName = _
            rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hZ⟩
        · exact ⟨_, _, _, by
            show (⟨natSuccA :: env.consts⟩ : ConLeche.Env).find? natSuccA.name = _
            rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl⟩))
    (hrd := lfp0_reads (by rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN)
      (fun ψ => by show denoteMeta _ _ _ 0 (.sort _) = _; rw [denoteMeta_sort]; rfl))
    (hrdC := lfp0_ctorReads (by rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN)
      (fun ψ => ⟨_, by show denoteMeta _ _ _ 0 (.sort _) = _; rw [denoteMeta_sort]⟩) fun j hj => by
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · refine ⟨natZeroA.toConstantVal, 0, ?_, rfl,
          ⟨natA.toConstantVal, _, by rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN,
            rfl⟩,
          .fvar 0 (.sort .zero), by decide, by decide, fun ψ => ⟨rfl, [], ?_, rfl⟩⟩
        · show (⟨natSuccA :: env.consts⟩ : ConLeche.Env).find? natZeroName = _
          rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; rw [hZ]; rfl
        · show denoteMeta _ _ _ 1 (.fvar 0 (.sort .zero)) = _
          rw [denoteMeta_fvar]; rfl
      · refine ⟨natSuccA.toConstantVal, 1, ?_, rfl,
          ⟨natA.toConstantVal, _, by rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN,
            rfl⟩,
          .forallE (.fvar 0 (.sort .zero)) (.fvar 0 (.sort .zero)) { pw := .never }, by decide,
          by decide, fun ψ => ⟨rfl, [(0, pwBit ψ .never, .bvar 0)], ?_, rfl⟩⟩
        · show (⟨natSuccA :: env.consts⟩ : ConLeche.Env).find? natSuccA.name = _
          rw [ConLeche.Env.find?_cons, ite_eq_left rfl]; rfl
        · show denoteMeta _ _ _ 1 (.forallE (.fvar 0 (.sort .zero)) (.fvar 0 (.sort .zero))
            { pw := .never }) = _
          simp [denoteMeta_forallE, ConLeche.Expr.instantiate1, denoteMeta_fvar, mkPisAV])
    (hnd := nodup_one _) (hlen := rfl)
    (hall := lfpAll_one (n := natName) (c := natA) rfl rfl
      (by rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN)
      (fun _ _ h => by injection h with _ h; subst h; rfl))
    (hown := lfpOwn_one (T := natName)
      (cs := [(natZeroA.toConstantVal, 0, 0), (natSuccA.toConstantVal, 0, 1)]) rfl rfl
      (by rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN)
      (by
        show List.filterMap (ctorLook (ConLeche.Env.find? ⟨natSuccA :: env.consts⟩) natName)
          [natZeroA.name, natSuccA.name] = _
        have hz : ConLeche.Env.find? ⟨natSuccA :: env.consts⟩ natZeroA.name = some natZeroA := by
          rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hZ
        simp only [List.filterMap_cons, List.filterMap_nil, ctorLook, hz,
          ConLeche.Env.find?_cons_self, Option.bind_some,
          ctorEntry_self (c₀ := natSuccA) (T := natName) rfl rfl rfl,
          ctorEntry_self (c₀ := natZeroA) (T := natName) rfl rfl rfl]
        rfl)
      ⟨0, [(natZeroA.toConstantVal, 0), (natSuccA.toConstantVal, 1)], rfl, rfl, fun j hj => by
        rcases (show j = 0 ∨ j = 1 by simp at hj; omega) with rfl | rfl
        · show (⟨natSuccA :: env.consts⟩ : ConLeche.Env).find? natZeroName = _
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
    (A := fun _ => AnnotTerm.const .natSucc []) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT natSuccA.name ψ
          = some (Term.const .natSucc []) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_ ?_)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_wellDenotedV (bitAgree_natSuccA ψ) ρ).mpr
      (WellDenotedV_bconst_type V .natSucc [] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AnnotTerm.BitAgree.interp_eq V (bitAgree_natSuccA ψ) ρ]
    exact bval_mem_type V .natSucc [] ρ
  · -- `nat_heads`, bespoke: the three leaves are the two prefix pins
    -- and the fresh one
    intro m₂ hac φ _ ρ
    have hZl : m₂.acval natZeroName (Level.substFn φ [] [])
        = AnnotTerm.const .natZero [] := by
      rw [hac, acvalWith_ne (by decide)]
      refine acval_basis_pinned (m := mp.base2) hZ (by decide) ?_
      simp +decide [ConLeche.Verify.pinnedStructT]
    have hNl : m₂.acval natName (Level.substFn φ [] [])
        = AnnotTerm.const .nat [] := by
      rw [hac, acvalWith_ne (by decide)]
      refine acval_basis_pinned (m := mp.base2) hN (by decide) ?_
      simp +decide [ConLeche.Verify.pinnedStructT]
    have hSl : m₂.acval natSuccName (Level.substFn φ [] [])
        = AnnotTerm.const .natSucc [] := by
      rw [hac, show natSuccName = natSuccA.name from rfl,
        acvalWith_self]
    rw [hZl, hNl, hSl]
    exact ⟨by simpa [interp_const, bval] using
        (natzero_mem : (natzero : V) ∈ˢ omega),
      by simpa [interp_const, bval] using natSuccV_mem V⟩
  · exact fun m₂ hac φ => recRules_cons_fresh mp (c₀ := natSuccA)
      (hntc := fun _ h => nomatch h)
      hfresh (fun _ _ _ _ h => nomatch h) m₂ hac φ

/-! ### The two firing rules

The three telescope domains, named once: their readings are the
`SetModel/Value.lean` spaces up to `piR_zero_agree`, which is the whole
content of "the reading's numerals are the pin's". -/

/-- The motive binder's domain reading. -/
def natMotiveTy (ψ : Name → Nat) : AnnotTerm :=
  .pi 0 (pwBit ψ .never) (.const .nat []) (.sort (ψ uN))

/-- The step binder's domain reading. -/
def natStepTy (ψ : Name → Nat) : AnnotTerm :=
  .pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
    (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 3) (.app (.const .natSucc []) (.bvar 1))))

theorem natMotiveTy_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natMotiveTy ψ) = natMotiveSpace V (ψ uN) := by
  rw [natMotiveTy, interp_pi, natMotiveSpace]
  refine piR_zero_agree (show pwBit ψ ConLeche.PropWhen.never = 0
      ↔ ψ uN + 1 = 0 by rw [pwBit_never]; simp) (fun _ _ => rfl)

theorem natStepTy_interp (ψ : Name → Nat) (ρ : Nat → V) (M z : V) :
    interp V (cons z (cons M ρ)) (natStepTy ψ)
      = natStepSpace V (pwBit ψ (.ifAllZero [uN])) M := by
  rw [natStepTy, interp_pi, natStepSpace]
  simp only [interp_const, bval]
  refine piR_congr fun n hn => ?_
  rw [interp_pi]
  simp only [interp_app, interp_bvar, interp_const, cons, bval]
  exact piR_congr fun _ _ => by rw [natSuccV_app V hn]

/-- The `zero` rule's RHS reading. -/
def natZeroRa (ψ : Name → Nat) : AnnotTerm :=
  .lam (pwBit ψ (.ifAllZero [uN])) (natMotiveTy ψ)
    (.lam (pwBit ψ (.ifAllZero [uN]))
      (.app (.bvar 0) (.const .natZero []))
      (.lam (pwBit ψ (.ifAllZero [uN])) (natStepTy ψ) (.bvar 1)))

/-- The `succ` rule's RHS reading — the recursive occurrence is the
*fresh* leaf, so it reads to `.const .natRec [ψ u]`. -/
def natSuccRa (ψ : Name → Nat) : AnnotTerm :=
  .lam (pwBit ψ (.ifAllZero [uN])) (natMotiveTy ψ)
    (.lam (pwBit ψ (.ifAllZero [uN]))
      (.app (.bvar 0) (.const .natZero []))
      (.lam (pwBit ψ (.ifAllZero [uN])) (natStepTy ψ)
        (.lam (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
          (.app (.app (.bvar 1) (.bvar 0))
            (.app (.app (.app (.app (.const .natRec [ψ uN]) (.bvar 3))
              (.bvar 2)) (.bvar 1)) (.bvar 0))))))

theorem denoteMeta_natRec_zeroRhs (ψ : Name → Nat)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denoteMeta (acvalWith m.acval natRecA.name A)
        ⟨natRecA :: env.consts⟩ ψ 0 natRecZeroRule.rhs
      = some (natZeroRa ψ) := by
  obtain ⟨hNc, hZc, hSc⟩ :=
    denoteMeta_natRec_leaves (m := m) (A := A) ψ hN hZ hS
  rw [show natRecZeroRule.rhs = Expr.lam
      (Expr.forallE (.const natName [])
        (.sort (.param uN)) { pw := .never })
      (Expr.lam
        (.app (.bvar 0) (.const natZeroName []))
        (Expr.lam
          (Expr.forallE (.const natName [])
            (Expr.forallE
              (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))
              { pw := .ifAllZero [uN] })
            { pw := .ifAllZero [uN] })
          (.bvar 1) { pw := .ifAllZero [uN] })
        { pw := .ifAllZero [uN] })
      { pw := .ifAllZero [uN] } from rfl]
  simp [denoteMeta_lam, denoteMeta_forallE, denoteMeta_sort, denoteMeta_app,
    denoteMeta_fvar, Expr.instantiate1, hNc, hZc, hSc, Level.eval,
    natZeroRa, natMotiveTy, natStepTy]

theorem denoteMeta_natRec_succRhs (ψ : Name → Nat)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denoteMeta (acvalWith m.acval natRecA.name
        (fun ψ => AnnotTerm.const .natRec [ψ uN]))
        ⟨natRecA :: env.consts⟩ ψ 0 natRecSuccRule.rhs
      = some (natSuccRa ψ) := by
  obtain ⟨hNc, hZc, hSc⟩ :=
    denoteMeta_natRec_leaves (m := m)
      (A := fun ψ => AnnotTerm.const .natRec [ψ uN]) ψ hN hZ hS
  have hRc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval natRecA.name
          (fun ψ => AnnotTerm.const .natRec [ψ uN]))
        ⟨natRecA :: env.consts⟩ ψ d
        (.const (natName.str "rec") [.param uN])
        = some (AnnotTerm.const .natRec [ψ uN]) := by
    intro d
    have hf : (⟨natRecA :: env.consts⟩ : Env).find? (natName.str "rec")
        = some natRecA := by
      rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl
    rw [denoteMeta_const hf (by rfl),
      show natName.str "rec" = natRecA.name from rfl, acvalWith_self]
    show some (AnnotTerm.const .natRec
      [Level.substFn ψ natRecA.toConstantVal.levelParams
        [Level.param uN] uN]) = _
    rw [show Level.substFn ψ natRecA.toConstantVal.levelParams
        [Level.param uN] uN = ψ uN from rfl]
  rw [show natRecSuccRule.rhs = Expr.lam
      (Expr.forallE (.const natName [])
        (.sort (.param uN)) { pw := .never })
      (Expr.lam
        (.app (.bvar 0) (.const natZeroName []))
        (Expr.lam
          (Expr.forallE (.const natName [])
            (Expr.forallE
              (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))
              { pw := .ifAllZero [uN] })
            { pw := .ifAllZero [uN] })
          (Expr.lam (.const natName [])
            (.app (.app (.bvar 1) (.bvar 0))
              (.app (.app (.app (.app
                (.const (natName.str "rec") [.param uN]) (.bvar 3))
                (.bvar 2)) (.bvar 1)) (.bvar 0)))
            { pw := .ifAllZero [uN] })
          { pw := .ifAllZero [uN] })
        { pw := .ifAllZero [uN] })
      { pw := .ifAllZero [uN] } from rfl]
  simp [denoteMeta_lam, denoteMeta_forallE, denoteMeta_sort, denoteMeta_app,
    denoteMeta_fvar, Expr.instantiate1, hNc, hZc, hSc, hRc, Level.eval,
    natSuccRa, natMotiveTy, natStepTy]

/-- The step space's numeral is read only through its zero test. -/
theorem natStepSpace_bit_agree {b u : Nat} (hz : b = 0 ↔ u = 0)
    (M : V) : natStepSpace V b M = natStepSpace V u M := by
  rw [natStepSpace, natStepSpace]
  exact piR_zero_agree hz fun _ _ => piR_zero_agree hz fun _ _ => rfl

/-- The motive binder's domain is graded — no numeral is read. -/
theorem natMotiveTy_wellDenotedV (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (natMotiveTy ψ) :=
  ⟨⟨trivial, fun _ _ => trivial⟩,
    ⟨trivial, fun _ _ => trivial, fun h => by
      rw [pwBit_never] at h; exact nomatch h⟩⟩

/-- The step binder's domain is graded, under a motive membership: the
three residual fibre obligations are `natMotive_apply` at `n`, at
`n + 1`, and `piR_zero_mem_univZero`. -/
theorem natStepTy_wellDenotedV (ψ : Name → Nat) (ρ : Nat → V) (M z : V)
    (hM : M ∈ˢ natMotiveSpace V (ψ uN)) :
    WellDenotedV V (cons z (cons M ρ)) (natStepTy ψ) := by
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
  have hM' : M ∈ˢ piR (ψ uN + 1) (omega : V) fun _ => univ (ψ uN) := hM
  constructor
  · refine ⟨trivial, fun n hn => ?_⟩
    have hn' : n ∈ˢ (omega : V) := by
      simpa [interp_const, bval] using hn
    refine ⟨⟨trivial, trivial, ψ uN + 1, omega, fun _ => univ (ψ uN),
        by simpa [interp_bvar, cons] using hM',
        by simpa [interp_bvar, cons] using hn',
        fun h => absurd h (Nat.succ_ne_zero _)⟩,
      fun ih _ => ⟨trivial, ⟨trivial, trivial, 1, omega,
        fun _ => omega, natSuccV_mem V,
        by simpa [interp_bvar, cons] using hn',
        fun h => absurd h Nat.one_ne_zero⟩,
        ψ uN + 1, omega, fun _ => univ (ψ uN),
        by simpa [interp_bvar, cons] using hM',
        by rw [interp_app, interp_const, interp_bvar]
           show app (natSuccV V) _ ∈ˢ _
           rw [show cons ih (cons n (cons z (cons M ρ))) 1 = n from rfl,
             natSuccV_app V hn']
           exact natsucc_mem hn',
        fun h => absurd h (Nat.succ_ne_zero _)⟩⟩
  · refine ⟨trivial, fun n hn => ?_, fun hz n hn => ?_⟩
    · have hn' : n ∈ˢ (omega : V) := by
        simpa [interp_const, bval] using hn
      refine ⟨⟨trivial, trivial⟩,
        fun _ _ => ⟨trivial, ⟨trivial, trivial⟩⟩, fun hz ih _ => ?_⟩
      rw [hcod n ih, natSuccV_app V hn']
      have := hMn (natsucc n) (natsucc_mem hn')
      rw [(pwBit_ifAllZero_single ψ uN).mp hz, univ_zero] at this
      exact this
    · rw [interp_pi]
      rw [hz]
      exact piR_zero_mem_univZero

/-! ### The two RHS towers, interpreted and graded -/

theorem natZeroRa_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natZeroRa ψ)
      = lamR (pwBit ψ (.ifAllZero [uN])) (natMotiveSpace V (ψ uN))
          (fun M => lamR (pwBit ψ (.ifAllZero [uN])) (app M natzero)
            (fun z => lamR (pwBit ψ (.ifAllZero [uN]))
              (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
              (fun _ => z))) := by
  simp only [natZeroRa, interp_lam, interp_app, interp_bvar,
    interp_const, cons, bval, natMotiveTy_interp, natStepTy_interp]

theorem natSuccRa_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natSuccRa ψ)
      = lamR (pwBit ψ (.ifAllZero [uN])) (natMotiveSpace V (ψ uN))
          (fun M => lamR (pwBit ψ (.ifAllZero [uN])) (app M natzero)
            (fun z => lamR (pwBit ψ (.ifAllZero [uN]))
              (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
              (fun s => lamR (pwBit ψ (.ifAllZero [uN])) omega
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
theorem natRecSpine_wellDenoted {u : Nat} (ρ : Nat → V) {e1 e2 e3 e4 : AnnotTerm}
    (h1 : WellDenoted V ρ e1) (h2 : WellDenoted V ρ e2)
    (h3 : WellDenoted V ρ e3) (h4 : WellDenoted V ρ e4)
    (m1 : interp V ρ e1 ∈ˢ natMotiveSpace V u)
    (m2 : interp V ρ e2 ∈ˢ app (interp V ρ e1) natzero)
    (m3 : interp V ρ e3 ∈ˢ natStepSpace V u (interp V ρ e1))
    (m4 : interp V ρ e4 ∈ˢ (omega : V)) :
    WellDenoted V ρ
      (.app (.app (.app (.app (.const .natRec [u]) e1) e2) e3) e4) := by
  have hlv : ConLeche.Term.lv [u] 0 = u := rfl
  have d1 : interp V ρ (arrowA 1 (u + 1) natTyAV (.sort u))
      = natMotiveSpace V u := by
    simp [arrowA, natTyAV, AnnotTerm.lift, AnnotTerm.liftN, interp_pi,
      interp_const, interp_sort, bval, natMotiveSpace]
  have d2 : ∀ a1 : V, interp V (cons a1 ρ)
      (.app (.bvar 0) natZeroAV) = app a1 natzero := by
    intro a1
    simp [natZeroAV, interp_app, interp_bvar, interp_const, cons,
      bval]
  have d3 : ∀ a1 a2 : V, interp V (cons a2 (cons a1 ρ))
      (AnnotTerm.pi 1 u natTyAV (.pi u u (.app (.bvar 2) (.bvar 0))
        (.app (.bvar 3) (natSuccAV (.bvar 1)))))
      = natStepSpace V u a1 := by
    intro a1 a2
    rw [interp_pi, natStepSpace]
    simp only [natTyAV, interp_const, bval]
    refine piR_congr fun k hk => ?_
    rw [interp_pi]
    simp only [natSuccAV, interp_app, interp_bvar, interp_const,
      cons, bval]
    exact piR_congr fun _ _ => by rw [natSuccV_app V hk]
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
      · refine bconst_app_dataAV V .natRec [u] ρ rfl
          (by rw [hlv, d1]; exact m1) ?_
        rw [d2]; exact m2
    · refine bconst_app_data3 V .natRec [u] ρ rfl
        (by rw [hlv, d1]; exact m1) (by rw [d2]; exact m2) ?_
      rw [hlv, d3]; exact m3
  · refine bconst_app_data4 V .natRec [u] ρ rfl
      (by rw [hlv, d1]; exact m1) (by rw [d2]; exact m2)
      (by rw [hlv, d3]; exact m3) ?_
    rw [d4]; exact m4

/-- The spine is bit-valid: `AnnotValid`'s `.app` clause is
structural. -/
theorem natRecSpine_validV {u : Nat} (ρ : Nat → V)
    {e1 e2 e3 e4 : AnnotTerm}
    (h1 : AnnotValid V ρ e1) (h2 : AnnotValid V ρ e2)
    (h3 : AnnotValid V ρ e3) (h4 : AnnotValid V ρ e4) :
    AnnotValid V ρ
      (.app (.app (.app (.app (.const .natRec [u]) e1) e2) e3) e4) :=
  ⟨⟨⟨⟨trivial, h1⟩, h2⟩, h3⟩, h4⟩

/-- The `zero` rule's RHS tower is graded. -/
theorem natZeroRa_wellDenotedV (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (natZeroRa ψ) := by
  have hb : ∀ M : V, M ∈ˢ natMotiveSpace V (ψ uN) →
      pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0 →
      app M natzero ∈ˢ (univZero : V) := by
    intro M hM hz
    have hh := natMotive_apply V hM (natzero_mem (V := V))
    rw [(pwBit_ifAllZero_single ψ uN).mp hz, univ_zero] at hh
    exact hh
  have hzty : ∀ M : V, interp V (cons M ρ)
      (AnnotTerm.app (.bvar 0) (.const .natZero [])) = app M natzero := by
    intro M; simp [interp_app, interp_bvar, interp_const, cons, bval]
  constructor
  · rw [natZeroRa, WellDenoted_lam, natMotiveTy_interp]
    refine ⟨(natMotiveTy_wellDenotedV ψ ρ).1, fun M hM => ?_, ?_⟩
    · have hM' : M ∈ˢ piR (ψ uN + 1) (omega : V)
          fun _ => univ (ψ uN) := hM
      rw [WellDenoted_lam, hzty]
      refine ⟨⟨trivial, trivial, ψ uN + 1, omega, fun _ => univ (ψ uN),
          by simpa [interp_bvar, cons] using hM',
          by simpa [interp_const, bval]
            using (natzero_mem : (natzero : V) ∈ˢ omega),
          fun h => absurd h (Nat.succ_ne_zero _)⟩,
        fun z hz => ?_, ?_⟩
      · rw [WellDenoted_lam, natStepTy_interp]
        exact ⟨(natStepTy_wellDenotedV ψ ρ M z hM).1, fun _ _ => trivial,
          fun _ => app M natzero,
          fun _ _ => by simpa [interp_bvar, cons] using hz,
          fun h _ _ => hb M hM h⟩
      · refine ⟨fun _ => piR (pwBit ψ (.ifAllZero [uN]))
            (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
            (fun _ => app M natzero),
          fun z hz => ?_,
          fun h _ _ => by rw [h]; exact piR_zero_mem_univZero⟩
        rw [interp_lam, natStepTy_interp]
        exact lamR_mem fun _ _ => by simpa [interp_bvar, cons] using hz
    · refine ⟨fun M => piR (pwBit ψ (.ifAllZero [uN])) (app M natzero)
          (fun _ => piR (pwBit ψ (.ifAllZero [uN]))
            (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
            (fun _ => app M natzero)),
        fun M hM => ?_,
        fun h _ _ => by rw [h]; exact piR_zero_mem_univZero⟩
      rw [interp_lam, hzty]
      refine lamR_mem fun z hz => ?_
      rw [interp_lam, natStepTy_interp]
      exact lamR_mem fun _ _ => by simpa [interp_bvar, cons] using hz
  · rw [natZeroRa, AnnotValid_lam, natMotiveTy_interp]
    refine ⟨(natMotiveTy_wellDenotedV ψ ρ).2, fun M hM => ?_⟩
    rw [AnnotValid_lam, hzty]
    exact ⟨⟨trivial, trivial⟩, fun z hz =>
      ⟨(natStepTy_wellDenotedV ψ ρ M z hM).2, fun _ _ => trivial⟩⟩

set_option maxHeartbeats 1000000 in
/-- The `succ` rule's RHS tower is graded — the extra layer over the
`zero` rule's is the recursive spine, `natRecSpine_wellDenoted`. -/
theorem natSuccRa_wellDenotedV (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (natSuccRa ψ) := by
  have hzty : ∀ M : V, interp V (cons M ρ)
      (AnnotTerm.app (.bvar 0) (.const .natZero [])) = app M natzero := by
    intro M; simp [interp_app, interp_bvar, interp_const, cons, bval]
  have hfib : ∀ M : V, M ∈ˢ natMotiveSpace V (ψ uN) → ∀ n : V,
      n ∈ˢ (omega : V) →
      pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0 →
      app M n ∈ˢ (univZero : V) := by
    intro M hM n hn hz
    have hh := natMotive_apply V hM hn
    rw [(pwBit_ifAllZero_single ψ uN).mp hz, univ_zero] at hh
    exact hh
  -- the fourth λ's body, at a fixed motive/minor/step
  have body : ∀ (M z s : V), M ∈ˢ natMotiveSpace V (ψ uN) →
      z ∈ˢ app M natzero →
      s ∈ˢ natStepSpace V (pwBit ψ (.ifAllZero [uN])) M →
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
    have hs' : s ∈ˢ natStepSpace V (ψ uN) M := by
      rwa [natStepSpace_bit_agree (pwBit_ifAllZero_single ψ uN)] at hs
    have hs'' : s ∈ˢ piR (ψ uN) (omega : V)
        fun k => piR (ψ uN) (app M k) fun _ => app M (natsucc k) := hs'
    have hsn : app s n ∈ˢ piR (ψ uN) (app M n)
        (fun _ => app M (natsucc n)) :=
      app_mem_piR (B := fun k => piR (ψ uN) (app M k)
        (fun _ => app M (natsucc k))) hs'' hn
        (fun h k hk => by rw [h]; exact piR_zero_mem_univZero)
    have hrec : app (app (app (app (natRecV V (ψ uN)) M) z) s) n
        ∈ˢ app M n := by
      rw [natRecV_app V hM hz hs' hn]
      exact natRecV_mem_fibre V hM hz hs' hn
    have espine : interp V (cons n (cons s (cons z (cons M ρ))))
        (.app (.app (.app (.app (.const .natRec [ψ uN]) (.bvar 3))
          (.bvar 2)) (.bvar 1)) (.bvar 0))
        = app (app (app (app (natRecV V (ψ uN)) M) z) s) n := by
      simp [interp_app, interp_bvar, interp_const, cons, bval,
        ConLeche.Term.lv]
    have eapp : interp V (cons n (cons s (cons z (cons M ρ))))
        (AnnotTerm.app (.bvar 1) (.bvar 0)) = app s n := by
      simp [interp_app, interp_bvar, cons]
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨⟨trivial, trivial, ψ uN, omega,
          fun k => piR (ψ uN) (app M k) (fun _ => app M (natsucc k)),
          by simpa [interp_bvar, cons] using hs'',
          by simpa [interp_bvar, cons] using hn,
          fun h k hk => by rw [h]; exact piR_zero_mem_univZero⟩,
        ?_, ?_⟩
      · refine natRecSpine_wellDenoted (u := ψ uN) _ trivial trivial trivial
          trivial ?_ ?_ ?_ ?_
        · simpa [interp_bvar, cons] using hM
        · simpa [interp_bvar, cons] using hz
        · simpa [interp_bvar, cons] using hs'
        · simpa [interp_bvar, cons] using hn
      · exact ⟨ψ uN, app M n, fun _ => app M (natsucc n),
          by rw [eapp]; exact hsn,
          by rw [espine]; exact hrec,
          fun h k hk => by
            have hh := natMotive_apply V hM (natsucc_mem hn)
            rw [h, univ_zero] at hh
            exact hh⟩
    · rw [interp_app, eapp, espine]
      exact app_mem_piR hsn hrec (fun h k hk => by
        have hh := natMotive_apply V hM (natsucc_mem hn)
        rw [h, univ_zero] at hh
        exact hh)
  constructor
  · rw [natSuccRa, WellDenoted_lam, natMotiveTy_interp]
    refine ⟨(natMotiveTy_wellDenotedV ψ ρ).1, fun M hM => ?_, ?_⟩
    · have hM' : M ∈ˢ piR (ψ uN + 1) (omega : V)
          fun _ => univ (ψ uN) := hM
      rw [WellDenoted_lam, hzty]
      refine ⟨⟨trivial, trivial, ψ uN + 1, omega, fun _ => univ (ψ uN),
          by simpa [interp_bvar, cons] using hM',
          by simpa [interp_const, bval]
            using (natzero_mem : (natzero : V) ∈ˢ omega),
          fun h => absurd h (Nat.succ_ne_zero _)⟩,
        fun z hz => ?_, ?_⟩
      · rw [WellDenoted_lam, natStepTy_interp]
        refine ⟨(natStepTy_wellDenotedV ψ ρ M z hM).1, fun s hs => ?_, ?_⟩
        · rw [WellDenoted_lam]
          simp only [interp_const, bval]
          exact ⟨trivial, fun n hn => (body M z s hM hz hs n hn).1,
            fun n => app M (natsucc n),
            fun n hn => (body M z s hM hz hs n hn).2,
            fun h n hn => hfib M hM (natsucc n) (natsucc_mem hn) h⟩
        · refine ⟨fun _ => piR (pwBit ψ (.ifAllZero [uN])) omega
              (fun n => app M (natsucc n)),
            fun s hs => ?_,
            fun h _ _ => by rw [h]; exact piR_zero_mem_univZero⟩
          rw [interp_lam]
          simp only [interp_const, bval]
          exact lamR_mem fun n hn => (body M z s hM hz hs n hn).2
      · refine ⟨fun _ => piR (pwBit ψ (.ifAllZero [uN]))
            (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
            (fun _ => piR (pwBit ψ (.ifAllZero [uN])) omega
              (fun n => app M (natsucc n))),
          fun z hz => ?_,
          fun h _ _ => by rw [h]; exact piR_zero_mem_univZero⟩
        rw [interp_lam, natStepTy_interp]
        refine lamR_mem fun s hs => ?_
        rw [interp_lam]
        simp only [interp_const, bval]
        exact lamR_mem fun n hn => (body M z s hM hz hs n hn).2
    · refine ⟨fun M => piR (pwBit ψ (.ifAllZero [uN])) (app M natzero)
          (fun _ => piR (pwBit ψ (.ifAllZero [uN]))
            (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
            (fun _ => piR (pwBit ψ (.ifAllZero [uN])) omega
              (fun n => app M (natsucc n)))),
        fun M hM => ?_,
        fun h _ _ => by rw [h]; exact piR_zero_mem_univZero⟩
      rw [interp_lam, hzty]
      refine lamR_mem fun z hz => ?_
      rw [interp_lam, natStepTy_interp]
      refine lamR_mem fun s hs => ?_
      rw [interp_lam]
      simp only [interp_const, bval]
      exact lamR_mem fun n hn => (body M z s hM hz hs n hn).2
  · rw [natSuccRa, AnnotValid_lam, natMotiveTy_interp]
    refine ⟨(natMotiveTy_wellDenotedV ψ ρ).2, fun M hM => ?_⟩
    rw [AnnotValid_lam, hzty]
    refine ⟨⟨trivial, trivial⟩, fun z hz => ?_⟩
    rw [AnnotValid_lam, natStepTy_interp]
    refine ⟨(natStepTy_wellDenotedV ψ ρ M z hM).2, fun s hs => ?_⟩
    rw [AnnotValid_lam]
    exact ⟨trivial, fun n hn =>
      ⟨⟨trivial, trivial⟩, natRecSpine_validV _ trivial trivial trivial
        trivial⟩⟩

/-! ### The two rows

Both rules are `.plain` (ENDGAME F §3), so the `.nested` conjuncts are
`nomatch` at both.  What differs from a single fieldless rule is the
shape of the fired equality — `natrec_zero` at one rule, `natrec_succ` at the other
— and that the `succ` rule's right-hand side mentions the recursor
itself, read through the **fresh** leaf. -/

/-- The recursor's telescope, unpacked into the four memberships
`SetModel/Value.lean`'s laws are stated with. -/
theorem natRecTelescope (ψ : Name → Nat) (ρ : Nat → V)
    {xs : List AnnotTerm} (hxs : xs.length = 3) (tl rest : AnnotTerm)
    (hfit : TeleFitPA V ρ
      (.pi 0 (pwBit ψ (.ifAllZero [uN])) (natMotiveTy ψ)
        (.pi 0 (pwBit ψ (.ifAllZero [uN]))
          (.app (.bvar 0) (.const .natZero []))
          (.pi 0 (pwBit ψ (.ifAllZero [uN])) (natStepTy ψ)
            (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
              (.app (.bvar 3) (.bvar 0))))))
      (xs ++ [tl]) rest) :
    ∃ M z s : AnnotTerm, xs = [M, z, s] ∧
      interp V ρ M ∈ˢ natMotiveSpace V (ψ uN) ∧
      interp V ρ z ∈ˢ app (interp V ρ M) natzero ∧
      interp V ρ s ∈ˢ natStepSpace V (ψ uN) (interp V ρ M) ∧
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
  · simpa [AnnotTerm.inst, AnnotTerm.liftN_zero, interp_app, interp_bvar,
      interp_const, cons, bval] using h2
  · have h3' : interp V ρ s
        ∈ˢ natStepSpace V (pwBit ψ (.ifAllZero [uN])) (interp V ρ M) := by
      have heq : (piR (pwBit ψ (.ifAllZero [uN])) (omega : V) fun x =>
            piR (pwBit ψ (.ifAllZero [uN])) (app (interp V ρ M) x)
              fun _ => app (interp V ρ M) (app (natSuccV V) x))
          = piR (pwBit ψ (.ifAllZero [uN])) omega fun n =>
            piR (pwBit ψ (.ifAllZero [uN])) (app (interp V ρ M) n)
              fun _ => app (interp V ρ M) (natsucc n) :=
        piR_congr fun n hn =>
          piR_congr fun _ _ => by rw [natSuccV_app V hn]
      rw [natStepSpace, ← heq]
      simpa [AnnotTerm.inst, AnnotTerm.liftN_zero, natStepTy,
        interp_liftN2_inst1, interp_liftN3_inst2, interp_pi,
        interp_app, interp_bvar, interp_const, cons_zero, cons_succ,
        bval] using h3
    rwa [natStepSpace_bit_agree (pwBit_ifAllZero_single ψ uN)] at h3'
  · simpa [AnnotTerm.inst, AnnotTerm.liftN_zero, interp_const, bval]
      using h4

/-- The `zero` tower's product membership. -/
theorem natZeroRa_mem (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natZeroRa ψ)
      ∈ˢ piR (pwBit ψ (.ifAllZero [uN])) (natMotiveSpace V (ψ uN))
        (fun M => piR (pwBit ψ (.ifAllZero [uN])) (app M natzero)
          (fun _ => piR (pwBit ψ (.ifAllZero [uN]))
            (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
            (fun _ => app M natzero))) := by
  rw [natZeroRa_interp]
  exact lamR_mem fun _ _ => lamR_mem fun z hz => lamR_mem fun _ _ => hz

/-- The `succ` tower's product membership. -/
theorem natSuccRa_mem (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (natSuccRa ψ)
      ∈ˢ piR (pwBit ψ (.ifAllZero [uN])) (natMotiveSpace V (ψ uN))
        (fun M => piR (pwBit ψ (.ifAllZero [uN])) (app M natzero)
          (fun _ => piR (pwBit ψ (.ifAllZero [uN]))
            (natStepSpace V (pwBit ψ (.ifAllZero [uN])) M)
            (fun _ => piR (pwBit ψ (.ifAllZero [uN])) omega
              (fun n => app M (natsucc n))))) := by
  rw [natSuccRa_interp]
  refine lamR_mem fun M hM => lamR_mem fun z hz =>
    lamR_mem fun s hs => lamR_mem fun n hn => ?_
  have hs' : s ∈ˢ natStepSpace V (ψ uN) M := by
    rwa [natStepSpace_bit_agree (pwBit_ifAllZero_single ψ uN)] at hs
  have hs'' : s ∈ˢ piR (ψ uN) (omega : V)
      fun k => piR (ψ uN) (app M k) fun _ => app M (natsucc k) := hs'
  have hsn := app_mem_piR (B := fun k => piR (ψ uN) (app M k)
      (fun _ => app M (natsucc k))) hs'' hn
    (fun h k hk => by rw [h]; exact piR_zero_mem_univZero)
  refine app_mem_piR hsn ?_ (fun h k hk => by
    have hh := natMotive_apply V hM (natsucc_mem hn)
    rw [h, univ_zero] at hh
    exact hh)
  rw [natRecV_app V hM hz hs' hn]
  exact natRecV_mem_fibre V hM hz hs' hn

/-- The `zero` rule's transport: three `WellDenoted_app` steps over
`natZeroRa_mem`. -/
theorem natZeroRa_transport (ψ : Name → Nat) (ρ : Nat → V)
    {M z s : AnnotTerm}
    (hM : interp V ρ M ∈ˢ natMotiveSpace V (ψ uN))
    (hz : interp V ρ z ∈ˢ app (interp V ρ M) natzero)
    (hs : interp V ρ s
      ∈ˢ natStepSpace V (ψ uN) (interp V ρ M))
    (okM : WellDenotedV V ρ M) (okz : WellDenotedV V ρ z)
    (oks : WellDenotedV V ρ s) :
    WellDenotedV V ρ (.app (.app (.app (natZeroRa ψ) M) z) s) := by
  have hs' : interp V ρ s
      ∈ˢ natStepSpace V (pwBit ψ (.ifAllZero [uN]))
        (interp V ρ M) := by
    rwa [natStepSpace_bit_agree (pwBit_ifAllZero_single ψ uN)]
  have hzero : ∀ K : V, K ∈ˢ natMotiveSpace V (ψ uN) →
      pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0 →
      app K natzero ∈ˢ (univZero : V) := by
    intro K hK h
    have hh := natMotive_apply V hK (natzero_mem (V := V))
    rw [(pwBit_ifAllZero_single ψ uN).mp h, univ_zero] at hh
    exact hh
  have h1 := app_mem_piR (natZeroRa_mem ψ ρ) hM
    (fun h _ _ => by rw [h]; exact piR_zero_mem_univZero)
  have h2 := app_mem_piR h1 hz
    (fun h _ _ => by rw [h]; exact piR_zero_mem_univZero)
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_app]
    refine ⟨?_, oks.1, _, _, _, h2, hs', fun h _ _ =>
      hzero _ hM h⟩
    rw [WellDenoted_app]
    refine ⟨?_, okz.1, _, _, _, h1, hz, fun h _ _ => by
      rw [h]; exact piR_zero_mem_univZero⟩
    rw [WellDenoted_app]
    exact ⟨(natZeroRa_wellDenotedV ψ ρ).1, okM.1, _, _, _,
      natZeroRa_mem ψ ρ, hM,
      fun h _ _ => by rw [h]; exact piR_zero_mem_univZero⟩
  · exact ⟨⟨⟨(natZeroRa_wellDenotedV ψ ρ).2, okM.2⟩, okz.2⟩, oks.2⟩

/-- The `succ` rule's transport: four steps. -/
theorem natSuccRa_transport (ψ : Name → Nat) (ρ : Nat → V)
    {M z s n : AnnotTerm}
    (hM : interp V ρ M ∈ˢ natMotiveSpace V (ψ uN))
    (hz : interp V ρ z ∈ˢ app (interp V ρ M) natzero)
    (hs : interp V ρ s
      ∈ˢ natStepSpace V (ψ uN) (interp V ρ M))
    (hn : interp V ρ n ∈ˢ (omega : V))
    (okM : WellDenotedV V ρ M) (okz : WellDenotedV V ρ z)
    (oks : WellDenotedV V ρ s) (okn : WellDenotedV V ρ n) :
    WellDenotedV V ρ (.app (.app (.app (.app (natSuccRa ψ) M) z) s) n) := by
  have hs' : interp V ρ s
      ∈ˢ natStepSpace V (pwBit ψ (.ifAllZero [uN]))
        (interp V ρ M) := by
    rwa [natStepSpace_bit_agree (pwBit_ifAllZero_single ψ uN)]
  have h1 := app_mem_piR (natSuccRa_mem ψ ρ) hM
    (fun h _ _ => by rw [h]; exact piR_zero_mem_univZero)
  have h2 := app_mem_piR h1 hz
    (fun h _ _ => by rw [h]; exact piR_zero_mem_univZero)
  have h3 := app_mem_piR h2 hs'
    (fun h _ _ => by rw [h]; exact piR_zero_mem_univZero)
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_app]
    refine ⟨?_, okn.1, _, _, _, h3, hn, fun h k hk => ?_⟩
    · rw [WellDenoted_app]
      refine ⟨?_, oks.1, _, _, _, h2, hs', fun h _ _ => by
        rw [h]; exact piR_zero_mem_univZero⟩
      rw [WellDenoted_app]
      refine ⟨?_, okz.1, _, _, _, h1, hz, fun h _ _ => by
        rw [h]; exact piR_zero_mem_univZero⟩
      rw [WellDenoted_app]
      exact ⟨(natSuccRa_wellDenotedV ψ ρ).1, okM.1, _, _, _,
        natSuccRa_mem ψ ρ, hM,
        fun h _ _ => by rw [h]; exact piR_zero_mem_univZero⟩
    · have hh := natMotive_apply V hM (natsucc_mem hk)
      rw [(pwBit_ifAllZero_single ψ uN).mp h, univ_zero] at hh
      exact hh
  · exact ⟨⟨⟨⟨(natSuccRa_wellDenotedV ψ ρ).2, okM.2⟩, okz.2⟩, oks.2⟩, okn.2⟩

/-- Both rows share this: the recursor's instantiated type reading,
folded back into the two named domains. -/
theorem natRecTyRead (m₂ : EnvModel V ⟨natRecA :: env.consts⟩)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hac : m₂.acval = acvalWith m.acval natRecA.name A)
    (φ : Name → Nat) (us : List Level) {ψ : Name → Nat}
    (hψ : ψ = Level.substFn φ natRecA.toConstantVal.levelParams us) :
    denoteMeta m₂.acval ⟨natRecA :: env.consts⟩ φ 0
        (natRecA.toConstantVal.type.instantiateLevelParams
          natRecA.toConstantVal.levelParams us)
      = some (.pi 0 (pwBit ψ (.ifAllZero [uN])) (natMotiveTy ψ)
          (.pi 0 (pwBit ψ (.ifAllZero [uN]))
            (.app (.bvar 0) (.const .natZero []))
            (.pi 0 (pwBit ψ (.ifAllZero [uN])) (natStepTy ψ)
              (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .nat [])
                (.app (.bvar 3) (.bvar 0)))))) := by
  rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac,
    denoteMeta_natRecA_type (m := m) _ hN hZ hS, ← hψ]
  rfl

/-- **`Nat.rec`'s `zero` row.** -/
theorem natRecZeroLaw {m : EnvModel V env}
    (m₂ : EnvModel V ⟨natRecA :: env.consts⟩)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hac : m₂.acval = acvalWith m.acval natRecA.name
      (fun ψ => AnnotTerm.const .natRec [ψ uN]))
    (φ : Name → Nat) :
    RecRuleLaw m₂ φ natRecA.name natRecA.toConstantVal 3 3
      natRecZeroRule := by
  refine ⟨Nat.le_refl 3, fun us hus => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ natRecA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  refine ⟨natZeroRa ψ, ?_, natZeroRa_wellDenotedV ψ, ?_, ?_⟩
  · rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteMeta_natRec_zeroRhs (m := m) _ hN hZ hS]
  · intro _ _ h; exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev _ hnested hpin hTVa hTVja hfitR hfitC
  obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hys
  obtain rfl : TVa = _ := (Option.some.inj
    ((natRecTyRead (m := m) m₂ hN hZ hS hac φ us hψ).symm.trans
      hTVa)).symm
  obtain ⟨M, z, s, rfl, hM, hz, hs, -⟩ :=
    natRecTelescope ψ ρ hxs _ restR hfitR
  have hctorL : m₂.acval (RecRule.ctor natRecZeroRule)
      (Level.substFn φ cvj.levelParams usj)
      = AnnotTerm.const .natZero [] := by
    rw [show RecRule.ctor natRecZeroRule = natZeroName from rfl, hac,
      acvalWith_ne (by decide)]
    refine acval_basis_pinned (m := m) hZ (by decide) ?_
    simp +decide [ConLeche.Verify.pinnedStructT]
  have hrecL : m₂.acval natRecA.name
      (Level.substFn φ natRecA.toConstantVal.levelParams us)
      = AnnotTerm.const .natRec [ψ uN] := by
    rw [hac, acvalWith_self, hψ]
  refine ⟨?_, ?_⟩
  · simp only [show natRecZeroRule.ctorParams = 0 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      List.append_nil, AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil, hrecL,
      hctorL, interp_app, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero]
    rw [natRecV_app V hM hz hs (natzero_mem (V := V)), natrec_zero,
      natZeroRa_interp]
    by_cases hbz : pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0
    · rw [hbz, lamR_zero, app_pt, app_pt, app_pt]
      have hh := natMotive_apply V hM (natzero_mem (V := V))
      rw [(pwBit_ifAllZero_single ψ uN).mp hbz] at hh
      exact mem_univ_zero hh hz
    · rw [app_lamR_pos hbz hM, app_lamR_pos hbz hz,
        app_lamR_pos hbz (by
          rwa [← natStepSpace_bit_agree
            (pwBit_ifAllZero_single ψ uN)] at hs)]
  · intro hxsA _
    simp only [List.take]
    exact natZeroRa_transport ψ ρ hM hz hs
      (hxsA M (by simp)) (hxsA z (by simp)) (hxsA s (by simp))

/-- **`Nat.rec`'s `succ` row** — the RHS mentions the recursor, read
through the *fresh* leaf. -/
theorem natRecSuccLaw {m : EnvModel V env}
    (m₂ : EnvModel V ⟨natRecA :: env.consts⟩)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hac : m₂.acval = acvalWith m.acval natRecA.name
      (fun ψ => AnnotTerm.const .natRec [ψ uN]))
    (φ : Name → Nat) :
    RecRuleLaw m₂ φ natRecA.name natRecA.toConstantVal 3 3
      natRecSuccRule := by
  refine ⟨Nat.le_refl 3, fun us hus => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ natRecA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  refine ⟨natSuccRa ψ, ?_, natSuccRa_wellDenotedV ψ, ?_, ?_⟩
  · rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteMeta_natRec_succRhs (m := m) _ hN hZ hS]
  · intro _ _ h; exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev _ hnested hpin hTVa hTVja hfitR hfitC
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
      = AnnotTerm.const .natSucc [] := by
    rw [show RecRule.ctor natRecSuccRule = natSuccName from rfl, hac,
      acvalWith_ne (by decide)]
    refine acval_basis_pinned (m := m) hS (by decide) ?_
    simp +decide [ConLeche.Verify.pinnedStructT]
  have hrecL : m₂.acval natRecA.name
      (Level.substFn φ natRecA.toConstantVal.levelParams us)
      = AnnotTerm.const .natRec [ψ uN] := by
    rw [hac, acvalWith_self, hψ]
  -- `n`'s membership comes from the *constructor's* telescope
  have hcvj : cvj = natSuccA.toConstantVal := by
    have hS' : (⟨natRecA :: env.consts⟩ : Env).find? natSuccName
        = some natSuccA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hS
    rw [show RecRule.ctor natRecSuccRule = natSuccName from rfl,
      hS'] at hfj
    injection Option.some.inj hfj with a1 _ _
    exact a1.symm
  subst hcvj
  have hTVja' : TVja = .pi 0 (pwBit
      (Level.substFn φ natSuccA.toConstantVal.levelParams usj) .never)
      (.const .nat []) (.const .nat []) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ, hac,
      denoteMeta_natSuccTy (m := m) _ (by decide) hN] at hTVja
    exact (Option.some.inj hTVja).symm
  subst hTVja'
  cases hfitC with | cons hn _ =>
  have hn' : interp V ρ n ∈ˢ (omega : V) := by
    simpa [interp_const, bval] using hn
  have hs' : interp V ρ s ∈ˢ natStepSpace V (ψ uN) (interp V ρ M) :=
    hs
  refine ⟨?_, ?_⟩
  · simp only [List.take, List.drop, List.cons_append, List.nil_append,
      AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil, hrecL,
      hctorL, interp_app, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero, show natRecSuccRule.ctorParams = 0 from rfl]
    rw [natSuccV_app V hn',
      natRecV_app V hM hz hs' (natsucc_mem hn'), natrec_succ _ _ hn',
      natSuccRa_interp]
    by_cases hbz : pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0
    · rw [hbz, lamR_zero, app_pt, app_pt, app_pt, app_pt]
      have hh := natMotive_apply V hM (natsucc_mem hn')
      rw [(pwBit_ifAllZero_single ψ uN).mp hbz] at hh
      have hmem : app (app (interp V ρ s) (interp V ρ n))
          (natrec (interp V ρ z) (interp V ρ s) (interp V ρ n))
          ∈ˢ app (interp V ρ M) (natsucc (interp V ρ n)) := by
        have hsn := app_mem_piR (B := fun k =>
            piR (ψ uN) (app (interp V ρ M) k)
              (fun _ => app (interp V ρ M) (natsucc k)))
          hs' hn' (fun h k hk => by rw [h]; exact piR_zero_mem_univZero)
        exact app_mem_piR hsn
          (natRecV_mem_fibre V hM hz hs' hn')
          (fun h k hk => by
            have h2 := natMotive_apply V hM (natsucc_mem hn')
            rw [h, univ_zero] at h2
            exact h2)
      exact mem_univ_zero hh hmem
    · rw [app_lamR_pos hbz hM, app_lamR_pos hbz hz,
        app_lamR_pos hbz (by
          rwa [← natStepSpace_bit_agree
            (pwBit_ifAllZero_single ψ uN)] at hs'),
        app_lamR_pos hbz hn',
        natRecV_app V hM hz hs' hn']
  · intro hxsA hysA
    simp only [List.take, List.drop,
      show natRecSuccRule.ctorParams = 0 from rfl]
    exact natSuccRa_transport ψ ρ hM hz hs' hn'
      (hxsA M (by simp)) (hxsA z (by simp)) (hxsA s (by simp))
      (hysA n (by simp))

/-- **`Nat.rec`, installed at the P tier.** -/
theorem extendNatRec (mp : EnvModelM V μ env)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hfresh : env.find? natRecA.name = none)
    (hwf : EnvWF ⟨natRecA :: env.consts⟩) {ex : List Name} :
    CoverTo mp ex ⟨natRecA :: env.consts⟩ ex := by
  have hty := fun ψ =>
    denoteMeta_natRecA_type (m := mp.base2)
      (A := fun ψ => AnnotTerm.const .natRec [ψ uN]) ψ hN hZ hS
  refine coverTo_cons hfresh (fun _ _ h => nomatch h) (declStep_preserves_of_basis_rec_cons mp
    (A := fun ψ => AnnotTerm.const .natRec [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT natRecA.name ψ
          = some (Term.const .natRec [ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h)
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
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_wellDenotedV (bitAgree_natRecA ψ) ρ).mpr
      (WellDenotedV_bconst_type V .natRec [ψ uN] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AnnotTerm.BitAgree.interp_eq V (bitAgree_natRecA ψ) ρ]
    exact bval_mem_type V .natRec [ψ uN] ρ
  · intro m₂ hac φ
    refine recRules_cons_rec mp hfresh natRecA_eq m₂ hac φ ?_
    intro rl hrl _
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
  have hwf1 : EnvWF ⟨natA :: env.consts⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
  have hf2 : (⟨natA :: env.consts⟩ : Env).find? natZeroA.name = none :=
    Option.isNone_iff_eq_none.mp h2
  refine (extendNat mp hf1
    (by simp [ConLeche.natLitSupported, ConLeche.natZeroOk,
      show (⟨natA :: env.consts⟩ : Env).find? natZeroName = none
        from hf2]) hwf1).trans fun mp1 => ?_
  have hN1 : (⟨natA :: env.consts⟩ : Env).find? natName
      = some natA := by
    rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl
  have hwf2 : EnvWF ⟨natZeroA :: natA :: env.consts⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ natZeroA.toConstantVal.type = true
    have hf : (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natName
        = some natA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN1
    rw [show natZeroA.toConstantVal.type = Expr.const natName []
      from rfl]
    simp [Expr.constsResolve, hf]
  have hf3 : (⟨natZeroA :: natA :: env.consts⟩ : Env).find?
      natSuccA.name = none := Option.isNone_iff_eq_none.mp h3
  refine (extendNatZero mp1 hN1 hf2
    (by simp [ConLeche.natLitSupported, ConLeche.natSuccOk,
      show (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natSuccName
        = none from hf3]) hwf2 List.mem_cons_self).trans fun mp2 => ?_
  have hN2 : (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natName
      = some natA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN1
  have hZ2 : (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natZeroName
      = some natZeroA := by
    rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl
  have hwf3 : EnvWF ⟨natSuccA :: natZeroA :: natA :: env.consts⟩ := by
    refine EnvWF.cons hwf2 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ natSuccA.toConstantVal.type = true
    have hf : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩
        : Env).find? natName = some natA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN2
    rw [show natSuccA.toConstantVal.type
      = Expr.forallE (.const natName [])
        (.const natName []) { pw := .never } from rfl]
    simp [Expr.constsResolve, hf]
  refine (extendNatSucc mp2 hN2 hZ2 hf3 hwf3).trans fun mp3 => ?_
  have hN3 : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩
      : Env).find? natName = some natA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN2
  have hZ3 : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩
      : Env).find? natZeroName = some natZeroA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hZ2
  have hS3 : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩
      : Env).find? natSuccName = some natSuccA := by
    rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl
  have hf4 : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩
      : Env).find? natRecA.name = none :=
    Option.isNone_iff_eq_none.mp h4
  have hwf4 : EnvWF ⟨natRecA :: natSuccA :: natZeroA :: natA
      :: env.consts⟩ := by
    have hfN : (⟨natRecA :: natSuccA :: natZeroA :: natA
        :: env.consts⟩ : Env).find? natName = some natA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hN3
    have hfZ : (⟨natRecA :: natSuccA :: natZeroA :: natA
        :: env.consts⟩ : Env).find? natZeroName = some natZeroA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hZ3
    have hfS : (⟨natRecA :: natSuccA :: natZeroA :: natA
        :: env.consts⟩ : Env).find? natSuccName = some natSuccA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hS3
    refine EnvWF.cons hwf3 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), ?_,
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    · show Expr.constsResolve _ natRecA.toConstantVal.type = true
      rw [show natRecA.toConstantVal.type
          = Expr.forallE
              (Expr.forallE
                (.const natName []) (.sort (.param uN))
                { pw := .never })
              (Expr.forallE
                (.app (.bvar 0) (.const natZeroName []))
                (Expr.forallE
                  (Expr.forallE
                    (.const natName [])
                    (Expr.forallE
                      (.app (.bvar 2) (.bvar 0))
                      (.app (.bvar 3)
                        (.app (.const natSuccName []) (.bvar 1)))
                      { pw := .ifAllZero [uN] })
                    { pw := .ifAllZero [uN] })
                  (Expr.forallE
                    (.const natName []) (.app (.bvar 3) (.bvar 0))
                    { pw := .ifAllZero [uN] })
                  { pw := .ifAllZero [uN] })
                { pw := .ifAllZero [uN] })
              { pw := .ifAllZero [uN] } from rfl]
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
                :: env.consts⟩ : Env).find? (natName.str "rec")
                = some natRecA := by
              rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl
            simp only [natRecSuccRule, Expr.constsResolve, hfN, hfZ,
              hfS, hfR, Option.isSome_some, Bool.and_self]
        · exact nomatch hr''
  exact extendNatRec mp3 hN3 hZ3 hS3 hf4  hwf4

end Nat

end ConLeche.Model
