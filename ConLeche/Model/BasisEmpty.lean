module

public import ConLeche.Model.BasisStep

import ConLeche.Model.BasisLfp
public import ConLeche.Model.Cover
public section

/-!
# The `Empty` block, P tier: the type-reading recipe, executed once
(task #161, ENDGAME F)

The recipe for a basis constant's type, in three moves:

1. `show` the pinned `ConstantInfo`'s type as a literal `Expr` tree
   (`show … from rfl`) — the `denote` clauses are `match`es and will
   not reduce until the scrutinee is a constructor application;
2. walk it with `denote_forallE`/`denote_sort`/`denote_app`/
   `denote_fvar` and `Expr.instantiate1_eq_self` at every closed
   binder body, with the constant leaves supplied by
   `EnvModel.acval_pinned` (`Model/BasisCons.lean`);
3. the reading is `BConst.typeAV` on the nose, so `WellDenotedTy_bconst_type` grades it and
   `bval_mem_type` inhabits it.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  emptyA emptyRecA emptyName uN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## `Empty` -/

/-- The `Empty` former's type reading: `Sort 1`, which is
`BConst.typeAV .empty [1]` on the nose. -/
theorem denote_emptyA_type
    {acval : Name → (Name → Nat) → Term} (ψ : Name → Nat) :
    denote acval ⟨emptyA :: env.consts, env.tables⟩ ψ 0 emptyA.toConstantVal.type
      = some (BConst.typeAV .empty [1]) := by
  rw [show emptyA.toConstantVal.type = Expr.sort (.succ .zero) from rfl,
    denote_sort]
  rfl

/-- **`Empty`, installed at the P tier.** -/
theorem extendEmpty (mp : EnvModelM V μ env)
    (hfresh : env.find? emptyName = none)
    (hwf : EnvWF ⟨emptyA :: env.consts, env.tables⟩) :
    CoverStep mp ⟨emptyA :: env.consts, env.tables⟩ := by
  -- the pinned block's lfp clause is recorded at its former
  refine coverTo_addLfp (D := emptyLfp emptyName 1) (hag := fun _ h => Agrees.cons hfresh h)
    (hL := emptyLfp_clause 1 (fun _ _ => by unfold acvalWith; split; rfl; exact absurd rfl ‹_›)) (hst := lfp0_stored)
    (hrd := lfp0_reads (by rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl)
      (fun ψ => by show denote _ _ _ 0 (.sort _) = _; rw [denote_sort]; rfl))
    (hrdC := lfp0_ctorReads (by rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl)
      (fun ψ => ⟨_, by show denote _ _ _ 0 (.sort _) = _; rw [denote_sort]⟩) fun j hj => absurd hj (Nat.not_lt_zero j))
    (hcaps := lfp0_caps (by rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl)
      (fun _ h => absurd h Nat.one_ne_zero) (fun h => absurd h (by decide))
      (fun j hj => absurd hj (Nat.not_lt_zero j)))
    (hnd := nodup_one _) (hlen := rfl)
    (hall := lfpAll_one (n := emptyName) (c := emptyA) rfl rfl
      (by rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl)
      (fun _ _ h => by injection h with _ h; subst h; rfl))
    (hown := lfpOwn_former0 (c₀ := emptyA) rfl rfl rfl rfl rfl (by decide) fun _ => rfl)
    (hex := filter_not_mem_self _)
    (coverA_pend hfresh <| declStep_preserves_of_basis_cons mp
    (A := fun _ => Term.const .empty [1]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT emptyA.name ψ
          = some (Term.const .empty [1]) from rfl] at hp
        rw [← Option.some.inj hp]) (fun _ _ _ _ h => nomatch h))
    (fun _ _ _ => rfl)
    (fun _ _ => trivial)
    (fun ψ => ⟨_, denote_emptyA_type ψ⟩) ?_ ?_
    (hind := indStrictHead_cons (ab := fun _ => []) (s := fun _ => 1)
      (fun ψ => denote_emptyA_type ψ) fun _ _ ρ vs hsp => by
        cases vs with
        | nil => exact strict_empty
        | cons _ _ => exact hsp.elim))
  · intro ψ ta h ρ
    rw [denote_emptyA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact WellDenotedTy_bconst_type V .empty [1] ρ
  · intro ψ ta h ρ
    rw [denote_emptyA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval_mem_type V .empty [1] ρ

/-! ## `Empty.rec` -/

/-- **`Empty.rec`'s type reading.**  The four moves of the module
docstring; the leaves are `EnvModel.acval_pinned` at `Empty`. -/
theorem denote_emptyRecA_type {m : EnvModel V env}
    {A : (Name → Nat) → Term} (ψ : Name → Nat)
    (hE : env.find? emptyName = some emptyA) :
    denote (acvalWith m.acval emptyRecA.name A)
        ⟨emptyRecA :: env.consts, env.tables⟩ ψ 0 emptyRecA.toConstantVal.type
      = some (.pi (.pi (.const .empty [1]) (.sort (ψ uN)))
          (.pi (.const .empty [1])
            (.app (.bvar 1) (.bvar 0)))) := by
  have hpd : ConLeche.Verify.pinnedStructT emptyName ψ
      = some (Term.const .empty [1]) := by
    simp +decide [ConLeche.Verify.pinnedStructT]
  have hleaf : acvalWith m.acval emptyRecA.name A emptyName ψ
      = Term.const .empty [1] := by
    rw [acvalWith_ne (by decide)]
    exact EnvModel.acval_pinned _ hE (by decide) hpd
  have hEc : ∀ d : Nat,
      denote (acvalWith m.acval emptyRecA.name A)
          ⟨emptyRecA :: env.consts, env.tables⟩ ψ d (.const emptyName [])
        = some (Term.const .empty [1]) := by
    intro d
    have hf : (⟨emptyRecA :: env.consts, env.tables⟩ : Env).find? emptyName
        = some emptyA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hE
    rw [denote_levelless_const hf (by rfl), hleaf]
  rw [show emptyRecA.toConstantVal.type
      = Expr.forallE
          (Expr.forallE (.const emptyName [])
            (.sort (.param uN)))
          (Expr.forallE (.const emptyName [])
            (.app (.bvar 1) (.bvar 0))) from rfl]
  simp [denote_forallE, denote_sort, denote_app, denote_fvar,
    Expr.instantiate1, hEc, Level.eval]

/-- **The reading is `BConst.typeAV`.** -/
theorem emptyRecA_reading_eq (ψ : Name → Nat) :
    (Term.pi (.pi (.const .empty [1]) (.sort (ψ uN)))
        (.pi (.const .empty [1])
          (.app (.bvar 1) (.bvar 0))))
      = BConst.typeAV .emptyRec [1, ψ uN] := rfl

/-- **`Empty.rec`, installed at the P tier.** -/
theorem extendEmptyRec (mp : EnvModelM V μ env)
    (hE : env.find? emptyName = some emptyA)
    (hfresh : env.find? emptyRecA.name = none)
    (hwf : EnvWF ⟨emptyRecA :: env.consts, env.tables⟩) {ex : List Name} :
    CoverTo mp ex ⟨emptyRecA :: env.consts, env.tables⟩ ex := by
  have hty := fun ψ =>
    denote_emptyRecA_type (m := mp.base2)
      (A := fun ψ => Term.const .emptyRec [1, ψ uN]) ψ hE
  refine coverTo_cons hfresh (fun _ _ h => nomatch h) (declStep_preserves_of_basis_cons mp
    (A := fun ψ => Term.const .emptyRec [1, ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => by injection h with _ _ _ h4; exact h4 ▸ rfl)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT emptyRecA.name ψ
          = some (Term.const .emptyRec [1, ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp])
      (fun _ _ _ _ h => by injection h with _ _ _ h4
                           intro r hr; rw [← h4] at hr; exact nomatch hr))
    ?_
    (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [emptyRecA_reading_eq]
    exact WellDenotedTy_bconst_type V .emptyRec [1, ψ uN] ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [emptyRecA_reading_eq]
    exact bval_mem_type V .emptyRec [1, ψ uN] ρ

/-! ## The block

`BasisInstallRun` is a right-nested `∧` chain, so the walk is an
`obtain` and two steps — there is no fold to invert. -/

/-- **The `Empty` block, installed at the P tier.**  `BasisStepPB`'s
`emptyK` branch. -/
theorem declBasisPB_emptyK {env₂ : Env} (mp : EnvModelM V μ env)
    (h : ConLeche.Semantics.BasisInstallRun env ConLeche.BasisKind.emptyK.declsA env₂) :
    CoverStep mp env₂ := by
  rw [show ConLeche.BasisKind.emptyK.declsA = [emptyA, emptyRecA] from rfl]
    at h
  obtain ⟨h1, h2, hnil⟩ := h
  subst hnil
  have hf1 : env.find? emptyA.name = none :=
    Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨emptyA :: env.consts, env.tables⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
  refine (extendEmpty mp hf1 hwf1).trans fun mp1 => ?_
  have hE : (⟨emptyA :: env.consts, env.tables⟩ : Env).find? emptyName
      = some emptyA := by
    rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl
  have hf2 : (⟨emptyA :: env.consts, env.tables⟩ : Env).find? emptyRecA.name
      = none := Option.isNone_iff_eq_none.mp h2
  have hwf2 : EnvWF ⟨emptyRecA :: emptyA :: env.consts, env.tables⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq),
      (fun _ _ _ _ heq => by
        injection heq with _ _ _ h4
        subst h4
        intro r hr; exact nomatch hr),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ emptyRecA.toConstantVal.type = true
    simp only [show emptyRecA.toConstantVal.type
        = Expr.forallE
            (Expr.forallE (.const emptyName [])
              (.sort (.param uN)))
            (Expr.forallE (.const emptyName [])
              (.app (.bvar 1) (.bvar 0))) from rfl,
      Expr.constsResolve, Bool.and_eq_true, Option.isSome_iff_exists]
    have hf : (⟨emptyRecA :: emptyA :: env.consts, env.tables⟩ : Env).find?
        emptyName = some emptyA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]
      exact hE
    rw [hf]
    simp
  exact extendEmptyRec mp1 hE hf2 hwf2

end ConLeche.Model
