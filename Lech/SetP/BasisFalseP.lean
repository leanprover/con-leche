import Lech.SetP.BasisEmptyP

/-!
# The `False` block, P tier (task #181)

`Lech/SetP/BasisEmptyP.lean`'s recipe at the pinned `False` block
(`Lech/Kernel/Basis/False.lean`): `False` is `Empty.{0}` in the
built-in currency — the leaf `.const .empty [0]` reads to the empty
set at `Sort 0`, `False.rec`'s leaf is `.const .emptyRec [0, ψ u]` —
so every move below is the `Empty` module's with the level numeral `1`
replaced by `0`.  `BConst.type2`/`bval2_mem_type`/`AnnotOkP_bconst_type`
are stated at every level list, so nothing new is proved about the
built-ins; the type readings are recomputed at the `False` pins
(`denoteP_falseA_type`, `denoteP_falseRecA_type`) and `BitAgree`d to
`BConst.type2 .empty [0]` / `.emptyRec [0, ψ u]`.

The point of the pin is the capstone: `no_constant_of_False_P`
(`CapstoneP.lean`) reads the leaf's value off `basis_pinnedL` exactly as
`no_constant_of_Empty_P` does, so `no_proof_of_False_P` needs no
hypothesis about how a stream declared `False`.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  falseA falseRecA falseName uN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## `Empty` -/

/-- The `False` former's type reading: `Sort 0`, which is
`BConst.type2 .empty [0]` on the nose (no `BitAgree` needed — the
former has no binder, so there is no numeral to disagree about). -/
theorem denoteP_falseA_type
    {acval : Name → (Name → Nat) → AVExpr} (ψ : Name → Nat) :
    denoteP acval ⟨falseA :: env.consts⟩ ψ 0 falseA.toConstantVal.type
      = some (BConst.type2 .empty [0]) := by
  rw [show falseA.toConstantVal.type = Expr.sort .zero from rfl,
    denoteP_sort]
  rfl

/-- **`False`, installed at the P tier.** -/
theorem extendFalseP (mp : EnvS2PM V μ env)
    (hfresh : env.find? falseName = none)
    (hwf : EnvWF ⟨falseA :: env.consts⟩) :
    Nonempty (EnvS2PM V μ ⟨falseA :: env.consts⟩) := by
  refine nonempty_of_exists (declStepPM_of_basis_cons mp
    (A := fun _ => AVExpr.const .empty [0]) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHeadP.ofBasis hwf (fun _ => trivial) (fun _ => rfl)
      (fun ψ t hp => by
        rw [show Lech.TTVerify.pinnedDirectT falseA.name ψ
          = some (VExpr.const .empty [0]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, denoteP_falseA_type ψ⟩) ?_ ?_)
  · intro ψ ta h ρ
    rw [denoteP_falseA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact AnnotOkP_bconst_type V .empty [0] ρ
  · intro ψ ta h ρ
    rw [denoteP_falseA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval2_mem_type V .empty [0] ρ

/-! ## `False.rec` — the recipe at `Prop`

Two binders, three stored `PropWhen` pins — the same three as
`Empty.rec`'s (`.ifAllZero [u]`, `.never`, `.ifAllZero [u]`): the
motive's domain `False → Sort u` has sort `imax 0 (u+1) = u+1`, never
`Prop`; the two outer binders' types have sort `imax (u+1) u` and
`imax 0 u = u`, `Prop` exactly at `u = 0`.  The `pwBit` lemmas are
`BasisEmptyP.lean`'s. -/

/-- **`False.rec`'s type reading.**  The four moves of the module
docstring; the leaves are `acval_basis_pinned` at `Empty`. -/
theorem denoteP_falseRecA_type {m : EnvS2Core V env}
    {A : (Name → Nat) → AVExpr} (ψ : Name → Nat)
    (hE : env.find? falseName = some falseA) :
    denoteP (acvalWith m.acval falseRecA.name A)
        ⟨falseRecA :: env.consts⟩ ψ 0 falseRecA.toConstantVal.type
      = some (.pi 0 (pwBit ψ (.ifAllZero [uN]))
          (.pi 0 (pwBit ψ .never) (.const .empty [0]) (.sort (ψ uN)))
          (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .empty [0])
            (.app (.bvar 1) (.bvar 0)))) := by
  have hpd : Lech.TTVerify.pinnedDirectT falseName ψ
      = some (VExpr.const .empty [0]) := by
    simp +decide [Lech.TTVerify.pinnedDirectT]
  have hleaf : acvalWith m.acval falseRecA.name A falseName ψ
      = AVExpr.const .empty [0] := by
    rw [acvalWith_ne (by decide)]
    exact acval_basis_pinned hE (by decide) hpd
  have hEc : ∀ d : Nat,
      denoteP (acvalWith m.acval falseRecA.name A)
          ⟨falseRecA :: env.consts⟩ ψ d (.const falseName [])
        = some (AVExpr.const .empty [0]) := by
    intro d
    have hf : (⟨falseRecA :: env.consts⟩ : Env).find? falseName
        = some falseA := by
      rw [Lech.Env.find?_cons, if_neg (by decide)]; exact hE
    rw [denoteP_levelless_const hf (by rfl), hleaf]
  rw [show falseRecA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "motive")
          (Expr.forallE (Name.anonymous.str "t") (.const falseName [])
            (.sort (.param uN)) { bi := .default, pw := .never })
          (Expr.forallE (Name.anonymous.str "t") (.const falseName [])
            (.app (.bvar 1) (.bvar 0))
            { bi := .default, pw := .ifAllZero [uN] })
          { bi := .default, pw := .ifAllZero [uN] } from rfl]
  simp [denoteP_forallE, denoteP_sort, denoteP_app, denoteP_fvar,
    Expr.instantiate1, hEc, Level.eval]

/-- **The reading agrees with `BConst.type2` on every numeral anything
reads.**  Three binders, three `pwBit`s, three `type2` slots, and the
iffs are `pwBit_never` and `pwBit_ifAllZero_single` — nothing here is
chosen. -/
theorem bitAgree_falseRecA (ψ : Name → Nat) :
    AVExpr.BitAgree
      (.pi 0 (pwBit ψ (.ifAllZero [uN]))
        (.pi 0 (pwBit ψ .never) (.const .empty [0]) (.sort (ψ uN)))
        (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .empty [0])
          (.app (.bvar 1) (.bvar 0))))
      (BConst.type2 .emptyRec [0, ψ uN]) := by
  have hz : pwBit ψ (Lech.PropWhen.ifAllZero [uN]) = 0 ↔ ψ uN = 0 :=
    pwBit_ifAllZero_single ψ uN
  refine .pi hz (.pi ?_ (.const _ _) (.sort _))
    (.pi hz (.const _ _) (.app (.bvar 1) (.bvar 0)))
  rw [pwBit_never]
  simp

/-- **`False.rec`, installed at the P tier.** -/
theorem extendFalseRecP (mp : EnvS2PM V μ env)
    (hE : env.find? falseName = some falseA)
    (hfresh : env.find? falseRecA.name = none)
    (hwf : EnvWF ⟨falseRecA :: env.consts⟩) :
    Nonempty (EnvS2PM V μ ⟨falseRecA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteP_falseRecA_type (m := mp.base2)
      (A := fun ψ => AVExpr.const .emptyRec [0, ψ uN]) ψ hE
  refine nonempty_of_exists (declStepPM_of_basis_cons mp
    (A := fun ψ => AVExpr.const .emptyRec [0, ψ uN]) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => by injection h with _ _ _ h4; exact h4 ▸ rfl)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHeadP.ofBasis hwf (fun _ => trivial) (fun _ => rfl)
      (fun ψ t hp => by
        rw [show Lech.TTVerify.pinnedDirectT falseRecA.name ψ
          = some (VExpr.const .emptyRec [0, ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => by injection h with _ _ _ h4
                           intro r hr; rw [← h4] at hr; exact nomatch hr))
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_okP (bitAgree_falseRecA ψ) ρ).mpr
      (AnnotOkP_bconst_type V .emptyRec [0, ψ uN] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AVExpr.BitAgree.interp2_eq V (bitAgree_falseRecA ψ) ρ]
    exact bval2_mem_type V .emptyRec [0, ψ uN] ρ

/-! ## The block

The dispatch mirrors `declBasisS_emptyK (the `Empty` twin)` link for link, and drives the
two lanes in lockstep: each cons runs the v1 install first (for the
`EnvS` base and its `cval` equation) and then the P install on top of
it.  `BasisInstallRun` is a right-nested `∧` chain, so the walk is an
`obtain` and two steps — there is no fold to invert. -/

/-- **The `False` block, installed at the P tier.**  `BasisStepPB`'s
`falseK` branch. -/
theorem declBasisPB_falseK {env₂ : Env} (mp : EnvS2PM V μ env)
    (h : Lech.Semantics.BasisInstallRun env Lech.BasisKind.falseK.declsA env₂) :
    Nonempty (EnvS2PM V μ env₂) := by
  rw [show Lech.BasisKind.falseK.declsA = [falseA, falseRecA] from rfl]
    at h
  obtain ⟨h1, h2, hnil⟩ := h
  subst hnil
  have hf1 : env.find? falseA.name = none :=
    Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨falseA :: env.consts⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq), (fun _ heq => nomatch heq)⟩
  obtain ⟨mp1⟩ := extendFalseP mp hf1 hwf1
  have hE : (⟨falseA :: env.consts⟩ : Env).find? falseName
      = some falseA := by
    rw [Lech.Env.find?_cons]; exact if_pos rfl
  have hf2 : (⟨falseA :: env.consts⟩ : Env).find? falseRecA.name
      = none := Option.isNone_iff_eq_none.mp h2
  have hwf2 : EnvWF ⟨falseRecA :: falseA :: env.consts⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq),
      (fun _ _ _ _ heq => by
        injection heq with _ _ _ h4
        subst h4
        intro r hr; exact nomatch hr),
      (fun _ _ heq => nomatch heq), (fun _ heq => nomatch heq)⟩
    show Expr.constsResolve _ falseRecA.toConstantVal.type = true
    simp only [show falseRecA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "motive")
            (Expr.forallE (Name.anonymous.str "t") (.const falseName [])
              (.sort (.param uN)) { bi := .default, pw := .never })
            (Expr.forallE (Name.anonymous.str "t") (.const falseName [])
              (.app (.bvar 1) (.bvar 0))
              { bi := .default, pw := .ifAllZero [uN] })
            { bi := .default, pw := .ifAllZero [uN] } from rfl,
      Expr.constsResolve, Bool.and_eq_true, Option.isSome_iff_exists]
    have hf : (⟨falseRecA :: falseA :: env.consts⟩ : Env).find?
        falseName = some falseA := by
      rw [Lech.Env.find?_cons, if_neg (by decide)]
      exact hE
    rw [hf]
    simp
  exact extendFalseRecP mp1 hE hf2 hwf2

end Lech.SetP
