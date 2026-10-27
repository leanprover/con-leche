module

public import ConLeche.Model.BasisEmpty

import ConLeche.Model.BasisLfp
import ConLeche.Model.Cover
public section

/-!
# The `False` block, P tier (task #181)

`ConLeche/Model/BasisEmpty.lean`'s recipe at the pinned `False` block
(`ConLeche/Kernel/Basis/False.lean`): `False` is `Empty.{0}` in the
built-in currency — the leaf `.const .empty [0]` reads to the empty
set at `Sort 0`, `False.rec`'s leaf is `.const .emptyRec [0, ψ u]` —
so every move below is the `Empty` module's with the level numeral `1`
replaced by `0`.  `BConst.typeAV`/`bval_mem_type`/`WellDenoted_bconst_type`
are stated at every level list, so nothing new is proved about the
built-ins; the type readings are recomputed at the `False` pins
(`denote_falseA_type`, `denote_falseRecA_type`) and are
`BConst.typeAV .empty [0]` / `.emptyRec [0, ψ u]` on the nose.

The point of the pin is the capstone: `no_constant_of_False`
(`Model/Capstone.lean`) reads the leaf's value off `basis_pinned` exactly as
`no_constant_of_Empty` does, so `no_proof_of_False_pure` needs no
hypothesis about how a stream declared `False`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  falseA falseRecA falseName uN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## `Empty` -/

/-- The `False` former's type reading: `Sort 0`, which is
`BConst.typeAV .empty [0]` on the nose. -/
theorem denote_falseA_type
    {acval : Name → (Name → Nat) → Term} (ψ : Name → Nat) :
    denote acval ⟨falseA :: env.consts, env.tables⟩ ψ 0 falseA.toConstantVal.type
      = some (BConst.typeAV .empty [0]) := by
  rw [show falseA.toConstantVal.type = Expr.sort .zero from rfl,
    denote_sort]
  rfl

/-- **`False`, installed at the P tier.** -/
theorem extendFalse (mp : EnvModelM V μ env)
    (hfresh : env.find? falseName = none)
    (hwf : EnvWF ⟨falseA :: env.consts, env.tables⟩) :
    CoverStep mp ⟨falseA :: env.consts, env.tables⟩ := by
  -- the pinned block's lfp clause is recorded at its former
  refine coverTo_addLfp (D := emptyLfp falseName 0) (hag := fun _ h => Agrees.cons hfresh h)
    (hL := emptyLfp_clause 0 (fun _ _ => by unfold acvalWith; split; rfl; exact absurd rfl ‹_›)) (hst := lfp0_stored)
    (hrd := lfp0_reads (by rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl)
      (fun ψ => by show denote _ _ _ 0 (.sort _) = _; rw [denote_sort]; rfl))
    (hrdC := lfp0_ctorReads (by rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl)
      (fun ψ => ⟨_, by show denote _ _ _ 0 (.sort _) = _; rw [denote_sort]⟩) fun j hj => absurd hj (Nat.not_lt_zero j))
    (hcaps := lfp0_caps (by rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl)
      (fun ψ _ => by
        show ConLeche.PropWhen.holds ψ (ConLeche.PropWhen.ifAllZero []) = true
        rw [ConLeche.PropWhen.holds_ifAllZero]; rfl)
      (fun h => absurd h (by decide))
      (fun j hj => absurd hj (Nat.not_lt_zero j)))
    (hnd := nodup_one _) (hlen := rfl)
    (hall := lfpAll_one (n := falseName) (c := falseA) rfl rfl
      (by rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl)
      (fun _ _ h => by injection h with _ h; subst h; rfl))
    (hown := lfpOwn_former0 (c₀ := falseA) rfl rfl rfl rfl rfl (by decide) fun _ => rfl)
    (hex := filter_not_mem_self _)
    (coverA_pend hfresh <| declStep_preserves_of_basis_cons mp
    (A := fun _ => Term.const .empty [0]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT falseA.name ψ
          = some (Term.const .empty [0]) from rfl] at hp
        rw [← Option.some.inj hp]) (fun _ _ _ _ h => nomatch h))
    (fun _ _ _ => rfl)
    (fun _ _ => trivial)
    (fun ψ => ⟨_, denote_falseA_type ψ⟩) ?_ ?_
    (hind := indStrictHead_cons_prop (ab := fun _ => []) fun ψ => denote_falseA_type ψ))
  · intro ψ ta h ρ
    rw [denote_falseA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact WellDenotedTy_bconst_type V .empty [0] ρ
  · intro ψ ta h ρ
    rw [denote_falseA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval_mem_type V .empty [0] ρ

/-! ## `False.rec` — the recipe at `Prop` -/

/-- **`False.rec`'s type reading.**  The moves of `BasisEmpty`'s module
docstring; the leaves are `EnvModel.acval_pinned` at `Empty`. -/
theorem denote_falseRecA_type {m : EnvModel V env}
    {A : (Name → Nat) → Term} (ψ : Name → Nat)
    (hE : env.find? falseName = some falseA) :
    denote (acvalWith m.acval falseRecA.name A)
        ⟨falseRecA :: env.consts, env.tables⟩ ψ 0 falseRecA.toConstantVal.type
      = some (.pi (.pi (.const .empty [0]) (.sort (ψ uN)))
          (.pi (.const .empty [0])
            (.app (.bvar 1) (.bvar 0)))) := by
  have hpd : ConLeche.Verify.pinnedStructT falseName ψ
      = some (Term.const .empty [0]) := by
    simp +decide [ConLeche.Verify.pinnedStructT]
  have hleaf : acvalWith m.acval falseRecA.name A falseName ψ
      = Term.const .empty [0] := by
    rw [acvalWith_ne (by decide)]
    exact EnvModel.acval_pinned _ hE (by decide) hpd
  have hEc : ∀ d : Nat,
      denote (acvalWith m.acval falseRecA.name A)
          ⟨falseRecA :: env.consts, env.tables⟩ ψ d (.const falseName [])
        = some (Term.const .empty [0]) := by
    intro d
    have hf : (⟨falseRecA :: env.consts, env.tables⟩ : Env).find? falseName
        = some falseA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hE
    rw [denote_levelless_const hf (by rfl), hleaf]
  rw [show falseRecA.toConstantVal.type
      = Expr.forallE
          (Expr.forallE (.const falseName [])
            (.sort (.param uN)))
          (Expr.forallE (.const falseName [])
            (.app (.bvar 1) (.bvar 0))) from rfl]
  simp [denote_forallE, denote_sort, denote_app, denote_fvar,
    Expr.instantiate1, hEc, Level.eval]

/-- **The reading is `BConst.typeAV`.** -/
theorem falseRecA_reading_eq (ψ : Name → Nat) :
    (Term.pi (.pi (.const .empty [0]) (.sort (ψ uN)))
        (.pi (.const .empty [0])
          (.app (.bvar 1) (.bvar 0))))
      = BConst.typeAV .emptyRec [0, ψ uN] := rfl

/-- **`False.rec`, installed at the P tier.** -/
theorem extendFalseRec (mp : EnvModelM V μ env)
    (hE : env.find? falseName = some falseA)
    (hfresh : env.find? falseRecA.name = none)
    (hwf : EnvWF ⟨falseRecA :: env.consts, env.tables⟩) {ex : List Name} :
    CoverTo mp ex ⟨falseRecA :: env.consts, env.tables⟩ ex := by
  have hty := fun ψ =>
    denote_falseRecA_type (m := mp.base2)
      (A := fun ψ => Term.const .emptyRec [0, ψ uN]) ψ hE
  refine coverTo_cons hfresh (fun _ _ h => nomatch h) (declStep_preserves_of_basis_cons mp
    (A := fun ψ => Term.const .emptyRec [0, ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => by injection h with _ _ _ h4; exact h4 ▸ rfl)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT falseRecA.name ψ
          = some (Term.const .emptyRec [0, ψ uN]) from rfl] at hp
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
    rw [falseRecA_reading_eq]
    exact WellDenotedTy_bconst_type V .emptyRec [0, ψ uN] ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [falseRecA_reading_eq]
    exact bval_mem_type V .emptyRec [0, ψ uN] ρ

/-! ## The block

The dispatch mirrors `declBasisPB_emptyK` link for link.
`BasisInstallRun` is a right-nested `∧` chain, so the walk is an
`obtain` and two steps — there is no fold to invert. -/

/-- **The `False` block, installed at the P tier.**  `BasisStepPB`'s
`falseK` branch. -/
theorem declBasisPB_falseK {env₂ : Env} (mp : EnvModelM V μ env)
    (h : ConLeche.Semantics.BasisInstallRun env ConLeche.BasisKind.falseK.declsA env₂) :
    CoverStep mp env₂ := by
  rw [show ConLeche.BasisKind.falseK.declsA = [falseA, falseRecA] from rfl]
    at h
  obtain ⟨h1, h2, hnil⟩ := h
  subst hnil
  have hf1 : env.find? falseA.name = none :=
    Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨falseA :: env.consts, env.tables⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
  refine (extendFalse mp hf1 hwf1).trans fun mp1 => ?_
  have hE : (⟨falseA :: env.consts, env.tables⟩ : Env).find? falseName
      = some falseA := by
    rw [ConLeche.Env.find?_cons]; exact ite_eq_left rfl
  have hf2 : (⟨falseA :: env.consts, env.tables⟩ : Env).find? falseRecA.name
      = none := Option.isNone_iff_eq_none.mp h2
  have hwf2 : EnvWF ⟨falseRecA :: falseA :: env.consts, env.tables⟩ := by
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
    show Expr.constsResolve _ falseRecA.toConstantVal.type = true
    simp only [show falseRecA.toConstantVal.type
        = Expr.forallE
            (Expr.forallE (.const falseName [])
              (.sort (.param uN)))
            (Expr.forallE (.const falseName [])
              (.app (.bvar 1) (.bvar 0))) from rfl,
      Expr.constsResolve, Bool.and_eq_true, Option.isSome_iff_exists]
    have hf : (⟨falseRecA :: falseA :: env.consts, env.tables⟩ : Env).find?
        falseName = some falseA := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]
      exact hE
    rw [hf]
    simp
  exact extendFalseRec mp1 hE hf2 hwf2

end ConLeche.Model
