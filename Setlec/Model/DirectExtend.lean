import Setlec.Model.DirectParams
import Setlec.Model.Extend.Model

/-!
# Installing a direct simple structure into the model

`checkDirectStruct` (`Setlec/Kernel/Checker.lean`) installs, in order,
the type former's model companion, the type former, the constructor's
companion, the constructor, the recursor with its rule, and then per
field a projection companion and the projection function.  This module
supplies the model-side counterpart of each step.

The **companions** are opaque constants of the same type carrying the
same value; installing them is uniform, so it is factored out here
(`extend_direct_companion`).  They are what makes the environment
invariant's modeled-value bridges (`ModeledOk`) hold verbatim for a
directly installed block: the direct path is its own preprocessor.
-/

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-! ### The per-field universe walk -/

/-- Inversion of the field-universe walk: every field's domain was
inferred, its sort ensured, and that sort checked `≤` the structure's
result sort. -/
theorem checkDirectFieldUniv_inv {env : Env} {F : Nat} {s : Level}
    {nP : Nat} {fvs : List Expr} :
    ∀ (k : Nat),
      checkDirectFieldUniv (fueledOps F) env s nP fvs k = .ok () →
      ∀ j, j < k → ∃ fv ty u, fvs[j]? = some fv ∧
        inferTypeCore env F (nP + j) (Expr.fvarTypeD fv) = .ok ty ∧
        ensureSortCore env F (nP + j) ty = .ok u ∧
        Level.leq u s = some true := by
  intro k
  induction k with
  | zero => intro _ j hj; exact absurd hj (by omega)
  | succ k ih =>
    intro h j hj
    rw [checkDirectFieldUniv] at h
    simp only [fueledOps_inferType, fueledOps_ensureSort, Bind.bind,
      Except.bind, unwrapOr] at h
    cases hfv : fvs[k]? with
    | none => rw [hfv] at h; exact nomatch h
    | some fv =>
      rw [hfv] at h
      simp only [pure, Except.pure] at h
      cases hty : inferTypeCore env F (nP + k) (Expr.fvarTypeD fv) with
      | error _ => rw [hty] at h; exact nomatch h
      | ok ty =>
        rw [hty] at h
        dsimp only [] at h
        cases hu : ensureSortCore env F (nP + k) ty with
        | error _ => rw [hu] at h; exact nomatch h
        | ok u =>
          rw [hu] at h
          simp only [liftFueled] at h
          cases hle : Level.leq u s with
          | none => rw [hle] at h; exact nomatch h
          | some b =>
            rw [hle] at h
            cases b with
            | false =>
              simp only [pure, Except.pure, Bool.false_eq_true, if_false,
                throw, throwThe, MonadExceptOf.throw] at h
              exact nomatch h
            | true =>
              simp only [pure, Except.pure, if_true] at h
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
              · exact ih h j hj'
              · exact ⟨fv, ty, u, hfv, hty, hu, hle⟩

/-! ### Frames

Everything a per-binder soundness step needs at a frame, bundled: the
`inferType`/`ensureSort` claims all take the same five syntactic and
semantic inputs, and the field walk has to re-establish them at each
opened binder. -/

/-- The frame conditions of one expression. -/
structure FrameOk (V : Type u) [SetTheory V] (cval : ConstVal V) (env : Env)
    (φ : Name → Nat) (d : Nat) (ρ : Nat → V) (e : Expr) : Prop where
  ws : Expr.WScoped d e
  bb : e.looseBVarsBounded 0 = true
  lb : Expr.LeavesBounded e
  fv : FvarsOk V cval env φ d ρ e
  an : AnnotOk V cval env φ d ρ e
  it : ∃ P, interpExpr V cval env φ d ρ e = some P

/-- A `∀`'s domain inherits the frame. -/
theorem FrameOk.dom {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} {n : Name} {dom body : Expr} {mb : BinderMeta}
    (h : FrameOk V cval env φ d ρ (.forallE n dom body mb)) :
    FrameOk V cval env φ d ρ dom := by
  obtain ⟨hws, hbb, hlb, hfv, han, P, hit⟩ := h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
  simp only [AnnotOk] at han
  obtain ⟨handom, ⟨cod, hcod⟩, -⟩ := han
  rw [interpExpr, hcod] at hit
  cases hdom : interpExpr V cval env φ d ρ dom with
  | none => rw [hdom] at hit; exact nomatch hit
  | some A =>
    refine ⟨hws.1, hbb.1, ?_, ?_, handom, ⟨A, hdom⟩⟩
    · exact fun l hl => hlb l (by simp [Expr.fvarLeaves, hl])
    · exact FvarsOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hfv

/-- Opening a `∀` re-establishes the frame one binder up. -/
theorem FrameOk.body {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} {n : Name} {dom body : Expr} {mb : BinderMeta}
    {A x : V}
    (h : FrameOk V cval env φ d ρ (.forallE n dom body mb))
    (hdom : interpExpr V cval env φ d ρ dom = some A) (hx : x ∈ˢ A) :
    FrameOk V cval env φ (d + 1) (updV V ρ d x)
      (body.instantiate1 (.fvar d n dom)) := by
  obtain ⟨hws, hbb, hlb, hfv, han, -⟩ := h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
  simp only [AnnotOk] at han
  obtain ⟨handom, ⟨cod, hcod⟩, hcond⟩ := han
  obtain ⟨hAb, hwfact⟩ := hcond x A hdom hx
  obtain ⟨w, hwi, -⟩ := hwfact cod hcod
  have hlbdom : Expr.LeavesBounded dom :=
    fun l hl => hlb l (by simp [Expr.fvarLeaves, hl])
  have hbdom : dom.looseBVarsBounded 0 = true := hbb.1
  refine ⟨hws.1.instantiate1 0 hws.2,
    looseBVarsBounded_instantiate1 body 0 hbb.2, ?_, ?_, hAb, ⟨w, hwi⟩⟩
  · intro l hl
    rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact hlb l (by simp [Expr.fvarLeaves, hl'])
    · simp only [Expr.fvarLeaves, List.mem_cons] at hl'
      rcases hl' with rfl | hl'
      · exact hbdom
      · exact hlbdom l hl'
  · exact FvarsOk.instantiate1 hws.1
      (FvarsOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hfv)
      handom hdom hx body 0 hws.2
      (FvarsOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hfv)

/-! ### `FieldTele` from the per-field universe walk -/

/-- The field telescope is small at the structure's own sort: each
opened field domain interprets, and its inferred sort — checked `≤` the
result sort — puts it in that universe by cumulativity.  This is the
semantic content of the reference kernels' per-field universe bound. -/
theorem FieldTele_of_walk {env : Env} (m : EnvModel V env) {F : Nat}
    {φ : Name → Nat} {s : Level} :
    ∀ (k d : Nat) (ρ : Nat → V) (ty : Expr) (xFvs : List Expr) (rest : Expr),
      openPisAtFvars k ty d = some (xFvs, rest) →
      FrameOk V m.val env φ d ρ ty →
      (∀ j, j < k → ∃ fv tyj u, xFvs[j]? = some fv ∧
        inferTypeCore env F (d + j) (Expr.fvarTypeD fv) = .ok tyj ∧
        ensureSortCore env F (d + j) tyj = .ok u ∧
        Level.leq u s = some true) →
      FieldTele V m.val env φ (s.eval φ) k d ρ ty := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _; trivial
  | succ k ih =>
    intro d ρ ty xFvs rest hop hfr hwalk
    match ty with
    | .forallE n dom body mb =>
      simp only [openPisAtFvars] at hop
      cases hrec : openPisAtFvars k (body.instantiate1 (.fvar d n dom)) (d + 1) with
      | none => rw [hrec] at hop; exact nomatch hop
      | some q =>
        rw [hrec] at hop
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        -- the head field: its domain is the frame's domain
        obtain ⟨fv0, ty0, u0, hfv0, hinf, hens, hle⟩ :=
          hwalk 0 (by omega)
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hfv0
        obtain rfl := hfv0
        rw [Nat.add_zero] at hinf hens
        obtain ⟨hdws, hdbb, hdlb, hdfv, hdan, -⟩ := hfr.dom
        obtain ⟨⟨v, tv, hvi, htvi, hmem⟩, htyW, htyA⟩ :=
          inferTypeCore_sound m F hinf hdws hdbb hdlb hdfv hdan
        simp only [Expr.fvarTypeD] at hvi
        -- the inferred sort is a universe, and it is at most `s`
        have htyb : ty0.looseBVarsBounded 0 = true :=
          inferTypeCore_looseBVars m.wf F hinf hdws hdbb hdlb
        have htyLb : Expr.LeavesBounded ty0 := fun l hl =>
          hdlb l (inferTypeCore_fvarLeaves m.wf F hinf hdws l hl)
        have htyFv : FvarsOk V m.val env φ d ρ ty0 :=
          FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf F hinf hdws) hdfv
        have hens' := ensureSortCore_sound m F hens htyW htyb htyLb htyFv htyA
        rw [hens'] at htvi
        obtain rfl : tv = univ (u0.eval φ) := (Option.some.inj htvi).symm
        have hAu : v ∈ˢ (univ (s.eval φ) : V) :=
          univ_mono (Level.leq_sound hle φ) v hmem
        refine ⟨v, hvi, hAu, ?_⟩
        intro x hx
        refine ih (d + 1) (updV V ρ d x) _ q.1 q.2 hrec
          (hfr.body hvi hx) ?_
        intro j hj
        obtain ⟨fv, tyj, u, hfvj, hinfj, hensj, hlej⟩ := hwalk (j + 1) (by omega)
        simp only [List.getElem?_cons_succ] at hfvj
        refine ⟨fv, tyj, u, hfvj, ?_, ?_, hlej⟩
        · rw [show d + 1 + j = d + (j + 1) from by omega]; exact hinfj
        · rw [show d + 1 + j = d + (j + 1) from by omega]; exact hensj
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      exact nomatch hop

/-- Install a direct block's **model companion**: an opaque constant of
a given type carrying a given value.  An `axiomInfo` triggers none of
the inductive-kind obligations, so the only real inputs are the type's
syntactic well-formedness, the key membership, and the value's
level-parameter extensionality. -/
theorem extend_direct_companion {env : Env} (m : EnvModel V env)
    {n : Name} {lps : List Name} {ty : Expr} {v₀ : (Name → Nat) → V}
    (hfind' : env.find? n = none)
    (hnempty : n ≠ emptyName)
    (htf : ty.hasFvar = false)
    (htp : ty.allLevelParamsDefined lps = true)
    (htr : ty.constsResolve env = true)
    (htb : ty.looseBVarsBounded 0 = true)
    (hkey : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m.val env ψ ty = some T ∧ v₀ ψ ∈ˢ T)
    (hparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ lps, ψ₁ p = ψ₂ p) → v₀ ψ₁ = v₀ ψ₂)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) ty) :
    ∃ m' : EnvModel V ⟨.axiomInfo ⟨n, lps, ty⟩ :: env.consts⟩,
      (∀ ψ, m'.val n ψ = v₀ ψ) ∧
      (∀ n' ψ, n' ≠ n → m'.val n' ψ = m.val n' ψ) := by
  have hwf : ConstWF ⟨ConstantInfo.axiomInfo ⟨n, lps, ty⟩ :: env.consts⟩
      (.axiomInfo ⟨n, lps, ty⟩) := by
    refine ⟨htf, htp, Expr.constsResolve_mono htr, htb, ?_, ?_, ?_⟩
    · intro _ _ _ heq; exact nomatch heq
    · intro _ _ _ _ heq; exact nomatch heq
    · intro _ _ heq; exact nomatch heq
  exact extend_fresh m (.axiomInfo ⟨n, lps, ty⟩) v₀ hfind' hwf htr
    (fun _ _ _ heq => nomatch heq)
    (fun _ _ heq => nomatch heq)
    hkey hparams hAty
    (fun _ _ heq => nomatch heq)
    (fun _ _ _ heq => nomatch heq)
    (fun _ _ heq => nomatch heq)
    (fun heq => absurd heq hnempty)
    (fun hb _ => by simp [ConstantInfo.isBasis] at hb)
    (fun _ _ _ _ heq => nomatch heq)
    (fun _ _ _ _ _ _ _ heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq)
    (fun _ hk => by
      rcases hk with ⟨_, _, heq⟩ | ⟨_, _, _, heq⟩ <;> exact nomatch heq)
    (fun _ _ _ _ _ _ _ heq => nomatch heq)
    (fun _ heq _ => nomatch heq)
    (fun _ _ heq => nomatch heq)
    (fun _ _ heq => nomatch heq)
    (fun _ _ _ _ _ _ heq => nomatch heq)
    (fun _ _ _ _ _ _ heq => nomatch heq)

end Setlec
