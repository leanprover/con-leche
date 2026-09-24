module

import ConLeche.Model.Inductives.BlockData
public import ConLeche.Model.Inductives.BlockRep
import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Verify.Inductives.FixRec
import ConLeche.Model.Inductives.FixRecRead
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Shift
import ConLeche.Model.Inductives.StructRecSpine
import ConLeche.Model.Inductives.StructData
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLemmas
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Inductives.NestPosMono
import ConLeche.Model.Inductives.BlockLfpHoles
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.Inductives.StructBits
public section

/-!
# The fields with holes ARE the member-abstracted readings (lane HOLE2)

Charter item 2: the clause's fields are "the interpretation of [the]
constructor types with holes at the block's members … ordinary open terms
(members abstracted to fvars)".  `nestPos` walks exactly those terms: the
stored constructor type, its parameters instantiated at the canonical
variables `0 ..< nP`, its members' constants replaced by the holes
`nP ..< nP + k` (`nestAbstract`), its fields opened above the holes
(`Kernel/Inductives/Positivity.lean`).

This file relates that walk to the CONCRETE opening the constructor stage
reads (`BlockCtorDataI`: parameters at `0 ..< nP`, fields at
`nP ..< nP + nF`, no holes).  The bridge is one Expr operation,
`holeAbs`: the concrete term with the fields moved `k` slots up
(`Expr.shiftFromN`) and the members abstracted (`nestAbstract`).  It
commutes with opening a binder (`holeAbs_instantiate1`), so the walk's
telescope is the concrete one abstracted field by field, up to `fvar`
annotations (`Expr.ErasedEq`, which the reading ignores).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal NestCtx nestAbstract instPisWith)

universe w

/-! ## Constant replacement by variables commutes with opening -/

/-- Replacing constants by `fvar`s commutes with instantiation. -/
theorem Expr.replaceConsts_instantiate1 {f : Name → List Level → Option Expr}
    (hf : ∀ c us e, f c us = some e → ∃ i ty, e = .fvar i ty) :
    ∀ (e v : Expr) (k : Nat),
      (e.instantiate1 v k).replaceConsts f = (e.replaceConsts f).instantiate1 (v.replaceConsts f) k := by
  intro e
  induction e with
  | bvar i =>
    intro v k
    by_cases h1 : i = k
    · subst h1; simp [Expr.instantiate1, Expr.replaceConsts]
    · by_cases h2 : i > k
      · simp [Expr.instantiate1, Expr.replaceConsts, h1, h2]
      · simp [Expr.instantiate1, Expr.replaceConsts, h1, h2]
  | fvar idx ty _ => intro v k; simp [Expr.instantiate1, Expr.replaceConsts]
  | const n us =>
    intro v k
    simp only [Expr.instantiate1, Expr.replaceConsts]
    cases hfn : f n us with
    | none => rfl
    | some e =>
      obtain ⟨i, ty, rfl⟩ := hf n us e hfn
      rfl
  | _ => intro v k; simp_all [Expr.instantiate1, Expr.replaceConsts]

/-- Replacing constants keeps erasure-equality. -/
theorem Expr.ErasedEq.replaceConsts {f : Name → List Level → Option Expr} :
    ∀ {a b : Expr}, Expr.ErasedEq a b → Expr.ErasedEq (a.replaceConsts f) (b.replaceConsts f)
  | .bvar i, b, h => by
    match b, h with
    | .bvar j, h => exact h
  | .fvar i ty, b, h => by
    match b, h with
    | .fvar j ty', h => exact h
  | .sort u, b, h => by
    match b, h with
    | .sort u', h => exact h
  | .const n us, b, h => by
    match b, h with
    | .const n' us', h =>
      obtain ⟨rfl, rfl⟩ := h
      exact Expr.ErasedEq.rfl _
  | .app f₁ a₁, b, h => by
    match b, h with
    | .app f₂ a₂, h => exact ⟨Expr.ErasedEq.replaceConsts h.1, Expr.ErasedEq.replaceConsts h.2⟩
  | .lam t₁ b₁ m₁, b, h => by
    match b, h with
    | .lam t₂ b₂ m₂, h =>
      exact ⟨h.1, Expr.ErasedEq.replaceConsts h.2.1, Expr.ErasedEq.replaceConsts h.2.2⟩
  | .forallE t₁ b₁ m₁, b, h => by
    match b, h with
    | .forallE t₂ b₂ m₂, h =>
      exact ⟨h.1, Expr.ErasedEq.replaceConsts h.2.1, Expr.ErasedEq.replaceConsts h.2.2⟩
  | .letE t₁ v₁ b₁, b, h => by
    match b, h with
    | .letE t₂ v₂ b₂, h =>
      exact ⟨Expr.ErasedEq.replaceConsts h.1, Expr.ErasedEq.replaceConsts h.2.1,
        Expr.ErasedEq.replaceConsts h.2.2⟩
  | .lit l, b, h => by
    match b, h with
    | .lit l', h => exact h
  | .proj s i e, b, h => by
    match b, h with
    | .proj s' i' e', h => exact ⟨h.1, h.2.1, Expr.ErasedEq.replaceConsts h.2.2⟩

/-! ### `shiftFromN`, structurally -/

theorem Expr.shiftFromN_forallE (p : Nat) :
    ∀ (n : Nat) (a b : Expr) (m : ConLeche.BinderMeta),
      Expr.shiftFromN p n (.forallE a b m)
        = .forallE (Expr.shiftFromN p n a) (Expr.shiftFromN p n b) m
  | 0, _, _, _ => rfl
  | n + 1, a, b, m => by
    show Expr.shiftFrom p (Expr.shiftFromN p n (.forallE a b m)) = _
    rw [Expr.shiftFromN_forallE p n]; rfl

theorem Expr.shiftFromN_app (p : Nat) :
    ∀ (n : Nat) (a b : Expr),
      Expr.shiftFromN p n (.app a b) = .app (Expr.shiftFromN p n a) (Expr.shiftFromN p n b)
  | 0, _, _ => rfl
  | n + 1, a, b => by
    show Expr.shiftFrom p (Expr.shiftFromN p n (.app a b)) = _
    rw [Expr.shiftFromN_app p n]; rfl

theorem Expr.shiftFromN_const (p : Nat) :
    ∀ (n : Nat) (c : Name) (us : List Level), Expr.shiftFromN p n (.const c us) = .const c us
  | 0, _, _ => rfl
  | n + 1, c, us => by
    show Expr.shiftFrom p (Expr.shiftFromN p n (.const c us)) = _
    rw [Expr.shiftFromN_const p n]; rfl

theorem Expr.shiftFromN_fvar_ge' {p i : Nat} (hi : p ≤ i) :
    ∀ (n : Nat) (ty : Expr),
      Expr.shiftFromN p n (.fvar i ty) = .fvar (i + n) (Expr.shiftFromN p n ty)
  | 0, _ => rfl
  | n + 1, ty => by
    show Expr.shiftFrom p (Expr.shiftFromN p n (.fvar i ty)) = _
    rw [Expr.shiftFromN_fvar_ge' hi n ty]
    simp only [Expr.shiftFrom, show i + n ≥ p by omega, if_true]
    rfl

/-- `shiftFrom`, iterated, commutes with opening at an `fvar` above the cut. -/
theorem Expr.shiftFromN_instantiate1 {p d : Nat} (hpd : p ≤ d) {ty : Expr} :
    ∀ (n : Nat) (e : Expr) (k : Nat),
      Expr.shiftFromN p n (e.instantiate1 (.fvar d ty) k) =
        (Expr.shiftFromN p n e).instantiate1 (.fvar (d + n) (Expr.shiftFromN p n ty)) k
  | 0, e, k => rfl
  | n + 1, e, k => by
    show Expr.shiftFrom p (Expr.shiftFromN p n (e.instantiate1 (.fvar d ty) k)) = _
    rw [Expr.shiftFromN_instantiate1 hpd n e k, Expr.shiftFrom_instantiate1 (by omega)]
    rfl

/-! ## The walk's term, from the concrete one -/

/-- **The member abstraction of a concretely opened term**: the fields
(variables at or above `nP`) moved above the `k` member holes, the
members' constants replaced by their holes. -/
@[expose] def holeAbs (ctx : NestCtx) (holes : List Expr) (e : Expr) : Expr :=
  nestAbstract ctx holes (Expr.shiftFromN ctx.nP ctx.names.length e)

/-- **The member abstraction commutes with instantiation**, when the
holes are `fvar`s. -/
theorem nestAbstract_instantiate1 {ctx : NestCtx} {holes : List Expr}
    (hh : ∀ h ∈ holes, ∃ i ty, h = .fvar i ty) (e v : Expr) (k : Nat) :
    nestAbstract ctx holes (e.instantiate1 v k)
      = (nestAbstract ctx holes e).instantiate1 (nestAbstract ctx holes v) k := by
  unfold nestAbstract
  refine Expr.replaceConsts_instantiate1 ?_ e v k
  intro c us e' h
  split at h
  · split at h
    · exact hh e' (List.mem_of_getElem? h)
    · exact nomatch h
  · exact nomatch h

/-- **The member abstraction commutes with opening a field** — the
concrete field variable at `nP + j`, the walk's at `nP + k + j`. -/
theorem holeAbs_instantiate1 {ctx : NestCtx} {holes : List Expr}
    (hh : ∀ h ∈ holes, ∃ i ty, h = .fvar i ty) {j : Nat} {ty : Expr} (e : Expr) (k : Nat) :
    holeAbs ctx holes (e.instantiate1 (.fvar (ctx.nP + j) ty) k)
      = (holeAbs ctx holes e).instantiate1
          (.fvar (ctx.nP + j + ctx.names.length) (holeAbs ctx holes ty)) k := by
  unfold holeAbs
  rw [Expr.shiftFromN_instantiate1 (Nat.le_add_right _ _), nestAbstract_instantiate1 hh]
  rfl

/-! ### `holeAbs`, structurally -/

theorem holeAbs_forallE (ctx : NestCtx) (holes : List Expr) (ty body : Expr)
    (mb : ConLeche.BinderMeta) :
    holeAbs ctx holes (.forallE ty body mb)
      = .forallE (holeAbs ctx holes ty) (holeAbs ctx holes body) mb := by
  unfold holeAbs nestAbstract
  rw [Expr.shiftFromN_forallE]
  rfl

theorem holeAbs_app (ctx : NestCtx) (holes : List Expr) (f a : Expr) :
    holeAbs ctx holes (.app f a) = .app (holeAbs ctx holes f) (holeAbs ctx holes a) := by
  unfold holeAbs nestAbstract
  rw [Expr.shiftFromN_app]
  rfl

theorem holeAbs_mkAppN (ctx : NestCtx) (holes : List Expr) :
    ∀ (as : List Expr) (f : Expr),
      holeAbs ctx holes (Expr.mkAppN f as) = Expr.mkAppN (holeAbs ctx holes f) (as.map (holeAbs ctx holes))
  | [], _ => rfl
  | a :: as, f => by
    show holeAbs ctx holes (Expr.mkAppN (.app f a) as) = _
    rw [holeAbs_mkAppN ctx holes as (.app f a), holeAbs_app]
    rfl

/-- A field variable moves above the holes. -/
theorem holeAbs_fvar_ge (ctx : NestCtx) (holes : List Expr) {i : Nat} (hi : ctx.nP ≤ i) (ty : Expr) :
    holeAbs ctx holes (.fvar i ty) = .fvar (i + ctx.names.length) (holeAbs ctx holes ty) := by
  unfold holeAbs nestAbstract
  rw [Expr.shiftFromN_fvar_ge' hi]
  rfl

/-- A parameter variable stays (its annotation abstracted). -/
theorem holeAbs_fvar_lt (ctx : NestCtx) (holes : List Expr) {i : Nat} (hi : i < ctx.nP) (ty : Expr) :
    ∃ ty', holeAbs ctx holes (.fvar i ty) = .fvar i ty' := by
  obtain ⟨ty', h⟩ := Expr.shiftFromN_fvar ctx.nP ctx.names.length i ty
  rw [if_pos hi] at h
  unfold holeAbs nestAbstract
  rw [h]
  exact ⟨_, rfl⟩

/-! ## The walk's opening IS the concrete one, abstracted -/

/-- **Opening the abstracted telescope** at the walk's depth gives the
abstracted variables and body of the concrete opening. -/
theorem openPisAtFvars_holeAbs {ctx : NestCtx} {holes : List Expr}
    (hh : ∀ h ∈ holes, ∃ i ty, h = .fvar i ty) :
    ∀ (n : Nat) {e : Expr} {j : Nat} {xs : List Expr} {rest : Expr},
      openPisAtFvars n e (ctx.nP + j) = some (xs, rest) →
      openPisAtFvars n (holeAbs ctx holes e) (ctx.nP + ctx.names.length + j)
        = some (xs.map (holeAbs ctx holes), holeAbs ctx holes rest)
  | 0, e, j, xs, rest, h => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | n + 1, e, j, xs, rest, h => by
    match e, h with
    | .forallE dom body mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next fvs r hop =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hop' : openPisAtFvars n (body.instantiate1 (.fvar (ctx.nP + j) dom)) (ctx.nP + (j + 1))
            = some (fvs, r) := by rw [← Nat.add_assoc]; exact hop
        have ih := openPisAtFvars_holeAbs hh n hop'
        rw [holeAbs_instantiate1 hh body 0] at ih
        rw [holeAbs_forallE]
        simp only [openPisAtFvars]
        rw [show (holeAbs ctx holes body).instantiate1
              (.fvar (ctx.nP + ctx.names.length + j) (holeAbs ctx holes dom))
            = (holeAbs ctx holes body).instantiate1
              (.fvar (ctx.nP + j + ctx.names.length) (holeAbs ctx holes dom)) by
            rw [show ctx.nP + ctx.names.length + j = ctx.nP + j + ctx.names.length by omega],
          show ctx.nP + ctx.names.length + j + 1 = ctx.nP + ctx.names.length + (j + 1) by omega,
          ih]
        simp only [List.map_cons, Option.some.injEq, Prod.mk.injEq, and_true]
        rw [holeAbs_fvar_ge ctx holes (Nat.le_add_right _ _),
          show ctx.nP + j + ctx.names.length = ctx.nP + ctx.names.length + j by omega]
      · exact nomatch h

/-! ## Reading a Π-telescope and its abstraction together -/

/-- **A concretely opened telescope and its abstraction read in step**:
the same binder bits, the domains and bodies as the openings read. -/
theorem denoteMeta_holeAbs_tele {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {ctx : NestCtx} {holes : List Expr}
    (hh : ∀ h ∈ holes, ∃ i ty, h = .fvar i ty) :
    ∀ (n : Nat) {e : Expr} {j : Nat} {xs : List Expr} {rest : Expr},
      openPisAtFvars n e (ctx.nP + j) = some (xs, rest) →
      ∀ (cdoms adoms : Nat → AnnotTerm) (cB aB : AnnotTerm),
        (∀ i x, xs[i]? = some x →
          denoteMeta acval env φ (ctx.nP + j + i) x.fvarTypeD = some (cdoms i) ∧
          denoteMeta acval env φ (ctx.nP + ctx.names.length + j + i)
            (holeAbs ctx holes x.fvarTypeD) = some (adoms i)) →
        denoteMeta acval env φ (ctx.nP + j + n) rest = some cB →
        denoteMeta acval env φ (ctx.nP + ctx.names.length + j + n) (holeAbs ctx holes rest)
          = some aB →
        ∃ cg ag : List (Nat × Nat × AnnotTerm),
          denoteMeta acval env φ (ctx.nP + j) e = some (mkPisAV cg cB) ∧
          denoteMeta acval env φ (ctx.nP + ctx.names.length + j) (holeAbs ctx holes e)
            = some (mkPisAV ag aB) ∧
          cg.length = n ∧ ag.length = n ∧
          ag.map (fun d => (d.1, d.2.1)) = cg.map (fun d => (d.1, d.2.1)) ∧
          (∀ i, i < n → (cg.getD i default).2.2 = cdoms i ∧ (ag.getD i default).2.2 = adoms i)
  | 0, e, j, xs, rest, h, cdoms, adoms, cB, aB, _, hcB, haB => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨[], [], by simpa [mkPisAV] using hcB, by simpa [mkPisAV] using haB, rfl, rfl, rfl,
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | n + 1, e, j, xs, rest, h, cdoms, adoms, cB, aB, hdoms, hcB, haB => by
    match e, h with
    | .forallE dom body mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next fvs r hop =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hop' : openPisAtFvars n (body.instantiate1 (.fvar (ctx.nP + j) dom))
            (ctx.nP + (j + 1)) = some (fvs, r) := by rw [← Nat.add_assoc]; exact hop
        obtain ⟨hc0, ha0⟩ := hdoms 0 _ rfl
        simp only [Expr.fvarTypeD, Nat.add_zero] at hc0 ha0
        obtain ⟨cg, ag, hc, ha, hcl, hal, hbits, hd⟩ :=
          denoteMeta_holeAbs_tele hh n hop' (fun i => cdoms (i + 1)) (fun i => adoms (i + 1))
            cB aB (fun i x hx => by
              have := hdoms (i + 1) x (by simpa using hx)
              rw [show ctx.nP + (j + 1) + i = ctx.nP + j + (i + 1) by omega,
                show ctx.nP + ctx.names.length + (j + 1) + i
                  = ctx.nP + ctx.names.length + j + (i + 1) by omega]
              exact this)
            (by rw [show ctx.nP + (j + 1) + n = ctx.nP + j + (n + 1) by omega]; exact hcB)
            (by rw [show ctx.nP + ctx.names.length + (j + 1) + n
                  = ctx.nP + ctx.names.length + j + (n + 1) by omega]; exact haB)
        refine ⟨(0, pwBit φ mb.pw, cdoms 0) :: cg, (0, pwBit φ mb.pw, adoms 0) :: ag, ?_, ?_,
          by simp [hcl], by simp [hal], by simp [hbits], fun i hi => ?_⟩
        · rw [denoteMeta_forallE, hc0]
          simp only [Option.bind_eq_bind, Option.bind_some]
          rw [show ctx.nP + j + 1 = ctx.nP + (j + 1) by omega, hc]
          rfl
        · rw [holeAbs_forallE, denoteMeta_forallE, ha0]
          simp only [Option.bind_eq_bind, Option.bind_some]
          rw [show (holeAbs ctx holes body).instantiate1
                (.fvar (ctx.nP + ctx.names.length + j) (holeAbs ctx holes dom))
              = holeAbs ctx holes (body.instantiate1 (.fvar (ctx.nP + j) dom)) by
              rw [holeAbs_instantiate1 hh body 0,
                show ctx.nP + j + ctx.names.length = ctx.nP + ctx.names.length + j by omega],
            show ctx.nP + ctx.names.length + j + 1 = ctx.nP + ctx.names.length + (j + 1) by omega,
            ha]
          rfl
        · cases i with
          | zero => exact ⟨rfl, rfl⟩
          | succ i => exact hd i (by omega)
      · exact nomatch h

/-! ## A hole-free term: the abstraction only moves the fields -/

/-- Shifting keeps a term's constants. -/
theorem Expr.constsResolve_shiftFrom {env₀ : Env} {p : Nat} :
    ∀ (e : Expr), (Expr.shiftFrom p e).constsResolve env₀ = e.constsResolve env₀ := by
  intro e
  induction e with
  | fvar idx ty ih =>
    simp only [Expr.shiftFrom]
    split <;> simp [Expr.constsResolve, ih]
  | _ => simp_all [Expr.shiftFrom, Expr.constsResolve]

theorem Expr.constsResolve_shiftFromN {env₀ : Env} {p : Nat} :
    ∀ (n : Nat) (e : Expr), (Expr.shiftFromN p n e).constsResolve env₀ = e.constsResolve env₀
  | 0, _ => rfl
  | n + 1, e => by
    show (Expr.shiftFrom p (Expr.shiftFromN p n e)).constsResolve env₀ = _
    rw [Expr.constsResolve_shiftFrom, Expr.constsResolve_shiftFromN n e]

/-- **The member abstraction fixes a term resolving before the block**
(no member is stored there). -/
theorem nestAbstract_eq_self_of_resolve {ctx : NestCtx} {holes : List Expr} {env₀ : Env}
    (hfresh : ∀ c, c ∈ ctx.names → env₀.find? c = none) :
    ∀ (e : Expr), e.constsResolve env₀ = true → nestAbstract ctx holes e = e := by
  intro e
  induction e with
  | const c us =>
    intro h
    simp only [Expr.constsResolve, Option.isSome_iff_exists] at h
    obtain ⟨ci, hci⟩ := h
    unfold nestAbstract
    simp only [Expr.replaceConsts]
    split
    · split
      · next mm hmm =>
        have hmem : c ∈ ctx.names := by
          obtain ⟨hlt, hget, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hmm
          have := List.getElem_mem hlt
          simp only [beq_iff_eq] at hget
          rw [hget] at this; exact this
        rw [hfresh c hmem] at hci; exact nomatch hci
      · rfl
    · rfl
  | fvar idx ty ih =>
    intro h
    simp only [Expr.constsResolve] at h
    unfold nestAbstract at ih ⊢
    simp only [Expr.replaceConsts]
    rw [ih h]
  | app f a ihf iha =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    unfold nestAbstract at ihf iha ⊢
    simp only [Expr.replaceConsts]
    rw [ihf h.1, iha h.2]
  | lam ty b m iht ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    unfold nestAbstract at iht ihb ⊢
    simp only [Expr.replaceConsts]
    rw [iht h.1, ihb h.2]
  | forallE ty b m iht ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    unfold nestAbstract at iht ihb ⊢
    simp only [Expr.replaceConsts]
    rw [iht h.1, ihb h.2]
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    unfold nestAbstract at iht ihv ihb ⊢
    simp only [Expr.replaceConsts]
    rw [iht h.1.1, ihv h.1.2, ihb h.2]
  | proj s i e ih =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    unfold nestAbstract at ih ⊢
    simp only [Expr.replaceConsts]
    rw [ih h.2]
  | bvar _ => intro _; rfl
  | sort _ => intro _; rfl
  | lit _ => intro _; rfl

/-- **A term resolving before the block**: its abstraction is the shift
alone, so it reads lifted over the holes. -/
theorem denoteMeta_holeAbs_resolve {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {ctx : NestCtx} {holes : List Expr} {env₀ : Env}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    (hfresh : ∀ c, c ∈ ctx.names → env₀.find? c = none) {i : Nat} {e : Expr}
    (hres : e.constsResolve env₀ = true) (hw : Expr.WScoped (ctx.nP + i) e) :
    denoteMeta acval env φ (ctx.nP + ctx.names.length + i) (holeAbs ctx holes e)
      = (denoteMeta acval env φ (ctx.nP + i) e).map (AnnotTerm.liftN ctx.names.length · i) := by
  unfold holeAbs
  rw [nestAbstract_eq_self_of_resolve hfresh _
      (by rw [Expr.constsResolve_shiftFromN]; exact hres),
    show ctx.nP + ctx.names.length + i = ctx.nP + i + ctx.names.length by omega,
    denoteMeta_shiftFromN hacl _ (Nat.le_add_right _ _) hw, Nat.add_sub_cancel_left]

/-! ## A member applied: the hole applied -/

theorem findIdx?_beq_of_nodup {names : List Name} (hnd : names.Nodup) {t : Nat}
    (ht : t < names.length) : names.findIdx? (· == names.getD t .anonymous) = some t := by
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨ht, ?_, fun j hj => ?_⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  · simp only [beq_iff_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht,
      Option.getD_some]
    intro h
    exact (List.pairwise_iff_getElem.mp hnd) j t (by omega) ht hj h

/-- **The abstraction of a member's former** at the block's levels is the
member's hole. -/
theorem holeAbs_member {ctx : NestCtx} {holes : List Expr} (hnd : ctx.names.Nodup) {t : Nat}
    (ht : t < ctx.names.length) {tyt : Expr} (hhole : holes[t]? = some (.fvar (ctx.nP + t) tyt)) :
    holeAbs ctx holes (.const (ctx.names.getD t .anonymous) (ctx.lps.map .param))
      = .fvar (ctx.nP + t) tyt := by
  unfold holeAbs nestAbstract
  rw [Expr.shiftFromN_const]
  simp only [Expr.replaceConsts, beq_self_eq_true, if_true, findIdx?_beq_of_nodup hnd ht, hhole]
  rfl

/-- **A field reading a member, finitary**: its abstraction reads as the
member's hole applied to the parameter variables and the field's index
readings, lifted over the holes. -/
theorem denoteMeta_holeAbs_rec {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {ctx : NestCtx} {holes : List Expr} {env₀ : Env}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    (hfresh : ∀ c, c ∈ ctx.names → env₀.find? c = none) (hnd : ctx.names.Nodup)
    {t : Nat} (ht : t < ctx.names.length) {tyt : Expr}
    (hhole : holes[t]? = some (.fvar (ctx.nP + t) tyt)) {i : Nat} {e : Expr}
    (hfn : e.getAppFn = .const (ctx.names.getD t .anonymous) (ctx.lps.map .param))
    (hps : ∀ (p : Nat) (x : Expr), (e.getAppArgs.take ctx.nP)[p]? = some x → ∃ ty, x = .fvar p ty)
    (hlen : ctx.nP ≤ e.getAppArgs.length)
    (hres : ∀ a ∈ e.getAppArgs.drop ctx.nP, a.constsResolve env₀ = true)
    (hw : ∀ a ∈ e.getAppArgs.drop ctx.nP, Expr.WScoped (ctx.nP + i) a)
    {Eis : List AnnotTerm}
    (hEis : DenoteMetaSpine acval env φ (ctx.nP + i) (e.getAppArgs.drop ctx.nP) Eis) :
    denoteMeta acval env φ (ctx.nP + ctx.names.length + i) (holeAbs ctx holes e)
      = some (AnnotTerm.mkAppN (.bvar (i + (ctx.names.length - 1 - t)))
          (paramBvarsAt ctx.nP (ctx.nP + ctx.names.length + i) ++
            Eis.map (AnnotTerm.liftN ctx.names.length · i))) := by
  rw [← Expr.mkAppN_getApp e, holeAbs_mkAppN, hfn, holeAbs_member hnd ht hhole,
    ← List.take_append_drop ctx.nP e.getAppArgs, List.map_append]
  refine denoteMeta_mkAppN (DenoteMetaSpine.append ?_ ?_) ?_
  · -- the parameters: variables at their own indices
    have hsp := denoteMetaSpine_fvars (acval := acval) (env := env) (φ := φ)
      (ctx.nP + ctx.names.length + i) ((e.getAppArgs.take ctx.nP).map (holeAbs ctx holes)) 0
      (fun p x hx => by
        rw [List.getElem?_map] at hx
        cases hq : (e.getAppArgs.take ctx.nP)[p]? with
        | none => rw [hq] at hx; exact nomatch hx
        | some y =>
          rw [hq, Option.map_some, Option.some.injEq] at hx
          obtain ⟨ty, rfl⟩ := hps p y hq
          have hp : p < ctx.nP := by
            have := (List.getElem?_eq_some_iff.mp hq).1
            rw [List.length_take] at this; omega
          obtain ⟨ty', h⟩ := holeAbs_fvar_lt ctx holes hp ty
          exact ⟨ty', by rw [← hx, h, Nat.zero_add]⟩)
    have hl : ((e.getAppArgs.take ctx.nP).map (holeAbs ctx holes)).length = ctx.nP := by
      rw [List.length_map, List.length_take]; omega
    rw [hl] at hsp
    simpa [paramBvarsAt] using hsp
  · -- the index expressions: resolving before the block, lifted
    exact DenoteMetaSpine.map_map (f := id) (g := holeAbs ctx holes)
      (h := (AnnotTerm.liftN ctx.names.length · i)) (by simpa using hEis) fun a v ha hv => by
        rw [denoteMeta_holeAbs_resolve hacl hfresh (hres a ha) (hw a ha)]
        simp only [id] at hv
        rw [hv]; rfl
  · rw [denoteMeta_fvar]
    congr 2
    omega

/-! ## Peeling a read Π-telescope along its opening -/

/-- **A read telescope, peeled along its opening**: the body reads as
the reading's body, every opened variable's annotation as its domain. -/
theorem denoteMeta_peel {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat} :
    ∀ (n : Nat) {e : Expr} {D : Nat} {xs : List Expr} {rest : Expr}
      {gds : List (Nat × Nat × AnnotTerm)} {B : AnnotTerm},
      openPisAtFvars n e D = some (xs, rest) → gds.length = n →
      denoteMeta acval env φ D e = some (mkPisAV gds B) →
      denoteMeta acval env φ (D + n) rest = some B ∧
      ∀ l x, xs[l]? = some x → denoteMeta acval env φ (D + l) x.fvarTypeD = some (gds.getD l default).2.2
  | 0, e, D, xs, rest, gds, B, h, hl, hr => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    exact ⟨by simpa [mkPisAV] using hr, fun l x hx => nomatch hx⟩
  | n + 1, e, D, xs, rest, gds, B, h, hl, hr => by
    match e, h, gds, hl with
    | .forallE dom body mb, h, g :: gds, hl =>
      simp only [openPisAtFvars] at h
      split at h
      · next fvs r hop =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ta, ba, hta, hba, heq⟩ := denoteMeta_forallE_inv hr
        simp only [mkPisAV, AnnotTerm.pi.injEq] at heq
        obtain ⟨-, -, hg, rfl⟩ := heq
        obtain ⟨hB, hdoms⟩ := denoteMeta_peel n hop (by simpa using hl) hba
        refine ⟨by rwa [show D + 1 + n = D + (n + 1) by omega] at hB, fun l x hx => ?_⟩
        cases l with
        | zero =>
          obtain rfl : Expr.fvar D dom = x := by simpa using hx
          simp only [Expr.fvarTypeD, Nat.add_zero, List.getD_cons_zero]
          rw [hta, hg]
        | succ l =>
          have := hdoms l x (by simpa using hx)
          rwa [show D + 1 + l = D + (l + 1) by omega] at this
      · exact nomatch h

/-! ## A reflexive field: its telescope lifted, the hole under it -/

/-- The telescope lifted over the holes, entry by entry. -/
theorem liftTeleK_getD (n : Nat) :
    ∀ (i : Nat) (tl : List (Nat × Nat × AnnotTerm)) (l : Nat), l < tl.length →
      (BlockData.liftTeleK n i tl).getD l default
        = ((tl.getD l default).1, (tl.getD l default).2.1, (tl.getD l default).2.2.liftN n (i + l))
  | _, [], _, hl => absurd hl (Nat.not_lt_zero _)
  | i, _ :: _, 0, _ => by simp [BlockData.liftTeleK]
  | i, _ :: tl, l + 1, hl => by
    simp only [BlockData.liftTeleK, List.getD_cons_succ]
    rw [liftTeleK_getD n (i + 1) tl l (by simpa using hl),
      show i + 1 + l = i + (l + 1) by omega]

theorem liftTeleK_length (n : Nat) :
    ∀ (i : Nat) (tl : List (Nat × Nat × AnnotTerm)), (BlockData.liftTeleK n i tl).length = tl.length
  | _, [] => rfl
  | i, _ :: tl => by simp [BlockData.liftTeleK, liftTeleK_length n (i + 1) tl]

/-- Two telescopes with the same bits and the same domains are equal. -/
theorem tele_ext {g₁ g₂ : List (Nat × Nat × AnnotTerm)} (hlen : g₁.length = g₂.length)
    (hbits : g₁.map (fun d => (d.1, d.2.1)) = g₂.map (fun d => (d.1, d.2.1)))
    (hdoms : ∀ l, l < g₁.length → (g₁.getD l default).2.2 = (g₂.getD l default).2.2) :
    g₁ = g₂ := by
  refine List.ext_getElem hlen fun l h1 h2 => ?_
  have hb := congrArg (·[l]?) hbits
  simp only [List.getElem?_map, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
  have hd := hdoms l h1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at hd
  exact Prod.ext hb.1 (Prod.ext hb.2 hd)

theorem liftTeleK_bits (n : Nat) :
    ∀ (i : Nat) (tl : List (Nat × Nat × AnnotTerm)),
      (BlockData.liftTeleK n i tl).map (fun d => (d.1, d.2.1)) = tl.map (fun d => (d.1, d.2.1))
  | _, [] => rfl
  | i, _ :: tl => by simp [BlockData.liftTeleK, liftTeleK_bits n (i + 1) tl]

/-- **A field reading a member, reflexive**: its abstraction reads as its
telescope lifted over the holes, the member's hole applied under it. -/
theorem denoteMeta_holeAbs_refl {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {ctx : NestCtx} {holes : List Expr} {env₀ : Env}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    (hfresh : ∀ c, c ∈ ctx.names → env₀.find? c = none) (hnd : ctx.names.Nodup)
    (hh : ∀ h ∈ holes, ∃ i ty, h = .fvar i ty)
    {t : Nat} (ht : t < ctx.names.length) {tyt : Expr}
    (hhole : holes[t]? = some (.fvar (ctx.nP + t) tyt)) {i : Nat} {e : Expr}
    (hwe : Expr.WScoped (ctx.nP + i) e)
    {tl : List (Nat × Nat × AnnotTerm)} {cB : AnnotTerm}
    (hread : denoteMeta acval env φ (ctx.nP + i) e = some (mkPisAV tl cB))
    {afvs : List Expr} {body : Expr}
    (hop : openPisAtFvars tl.length e (ctx.nP + i) = some (afvs, body))
    (hafvs : ∀ a ∈ afvs, a.fvarTypeD.constsResolve env₀ = true)
    (hfn : body.getAppFn = .const (ctx.names.getD t .anonymous) (ctx.lps.map .param))
    (hps : ∀ (p : Nat) (x : Expr), (body.getAppArgs.take ctx.nP)[p]? = some x → ∃ ty, x = .fvar p ty)
    (hlen : ctx.nP ≤ body.getAppArgs.length)
    (hres : ∀ a ∈ body.getAppArgs.drop ctx.nP, a.constsResolve env₀ = true)
    {Eis : List AnnotTerm}
    (hEis : DenoteMetaSpine acval env φ (ctx.nP + i + tl.length) (body.getAppArgs.drop ctx.nP) Eis) :
    denoteMeta acval env φ (ctx.nP + ctx.names.length + i) (holeAbs ctx holes e)
      = some (mkPisAV (BlockData.liftTeleK ctx.names.length i tl)
          (AnnotTerm.mkAppN (.bvar (i + tl.length + (ctx.names.length - 1 - t)))
            (paramBvarsAt ctx.nP (ctx.nP + ctx.names.length + (i + tl.length)) ++
              Eis.map (AnnotTerm.liftN ctx.names.length · (i + tl.length))))) := by
  obtain ⟨hB, hdoms⟩ := denoteMeta_peel tl.length hop rfl hread
  have hwA := openPisAtFvars_typeWScoped tl.length hop hwe
  have hwB : Expr.WScoped (ctx.nP + i + tl.length) body :=
    (openPisAtFvars_WScoped tl.length e (ctx.nP + i) hop hwe).2
  have hwArgs : ∀ a ∈ body.getAppArgs.drop ctx.nP, Expr.WScoped (ctx.nP + (i + tl.length)) a := by
    intro a ha
    rw [← Expr.mkAppN_getApp body] at hwB
    rw [← Nat.add_assoc]
    exact (wScoped_mkAppN _ hwB).2 a (List.mem_of_mem_drop ha)
  have haB := denoteMeta_holeAbs_rec (holes := holes) hacl hfresh hnd ht hhole
    (i := i + tl.length) hfn hps hlen hres hwArgs (by rw [← Nat.add_assoc]; exact hEis)
  obtain ⟨cg, ag, hc, ha, hcl, hal, hbits, hd⟩ :=
    denoteMeta_holeAbs_tele (acval := acval) (env := env) (φ := φ) hh tl.length (j := i) hop
      (fun l => (tl.getD l default).2.2)
      (fun l => (tl.getD l default).2.2.liftN ctx.names.length (i + l)) cB _
      (fun l a hl => by
        refine ⟨hdoms l a hl, ?_⟩
        have hres' : a.fvarTypeD.constsResolve env₀ = true := hafvs a (List.mem_of_getElem? hl)
        rw [show ctx.nP + ctx.names.length + i + l = ctx.nP + ctx.names.length + (i + l) by omega,
          denoteMeta_holeAbs_resolve hacl hfresh hres'
            (by rw [← Nat.add_assoc]; exact hwA l a hl),
          ← Nat.add_assoc, hdoms l a hl]
        rfl)
      hB (by rw [show ctx.nP + ctx.names.length + i + tl.length
            = ctx.nP + ctx.names.length + (i + tl.length) by omega]; exact haB)
  have hcg : cg = tl := (mkPisAV_inj (by rw [hcl]) (Option.some.inj (hc.symm.trans hread))).1
  subst hcg
  have hag : ag = BlockData.liftTeleK ctx.names.length i cg := by
    refine tele_ext (by rw [hal, liftTeleK_length, hcl]) (by rw [hbits, liftTeleK_bits]) ?_
    intro l hl
    rw [(hd l (by omega)).2, liftTeleK_getD _ _ _ _ (by omega)]
  rw [ha, hag]

/-! ## The uniform block's constructors: `absF` IS the walk's reading -/

section BlockCtor

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {d : BlockData V}
  {lps : List Name}

/-- **Field `i` of a stored constructor, abstracted, reads as `absField`**
— the hole reading the clause records. -/
theorem blockField_holeRead {c j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM c)[j]? = some cA) (hcf : BlockCtorFacts m d lps c j cA)
    {ctx : NestCtx} (hnames : ctx.names = d.memberNames) (hlps : ctx.lps = lps)
    (hnP : ctx.nP = d.nP) (hk : d.k = d.memberNames.length)
    {holes : List Expr} (hh : ∀ h ∈ holes, ∃ i ty, h = .fvar i ty)
    (hholes : ∀ t, t < d.k → ∃ ty, holes[t]? = some (.fvar (d.nP + t) ty))
    (hnd : d.memberNames.Nodup) (hfresh : ∀ n ∈ d.memberNames, d.env₀.find? n = none)
    (htgt : ∀ l, l < cA.2 → d.tgts c j l < d.k)
    {crest : Expr} (hwc : Expr.WScoped d.nP crest)
    (hopX : openPisAtFvars cA.2 crest d.nP = some (d.xFvsF c j, d.xrestF c j))
    (ψ : Name → Nat) {i : Nat} {x : Expr} (hx : (d.xFvsF c j)[i]? = some x) :
    denoteMeta m.acval env ψ (d.nP + d.k + i) (holeAbs ctx holes x.fvarTypeD)
      = some (d.absField ψ c j i) := by
  obtain ⟨-, -, hD⟩ := hcf
  have hacl := m.acval_closed
  have hi : i < cA.2 := by rw [← hD.xLen]; exact (List.getElem?_eq_some_iff.mp hx).1
  have hks : i < (d.ksF c j).length := by rw [hD.ksLen]; exact hi
  have hjc : j < (d.ctorsM c).length := (List.getElem?_eq_some_iff.mp hcj).1
  have hrs : (d.rss c).getD j [] = rsOf (d.ksF c j) := rssOfK_getD hjc
  have hFssD : (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  have hTl : (d.tlss c ψ).getD j [] = d.tssF c j ψ := tlssOfR_fixCtorDataList_getD hcj
  have hEi : (d.Eiss c ψ).getD j [] = d.eissF c j ψ := eissOfR_fixCtorDataList_getD hcj
  have hwx : Expr.WScoped (d.nP + i) x.fvarTypeD :=
    openPisAtFvars_typeWScoped cA.2 hopX hwc i x hx
  have hfresh' : ∀ n, n ∈ ctx.names → d.env₀.find? n = none := by rw [hnames]; exact hfresh
  have hnd' : ctx.names.Nodup := by rw [hnames]; exact hnd
  have hdepth : d.nP + d.k + i = ctx.nP + ctx.names.length + i := by
    rw [hnP, hnames, ← hk]
  rw [hdepth]
  unfold BlockData.absField
  rcases hD.opened.kinds i hi with hkd | hkd | hkd
  · -- a hole-free field
    have hr : ((d.rss c).getD j []).getD i false = false := by
      rw [hrs]
      cases h : (rsOf (d.ksF c j)).getD i false with
      | false => rfl
      | true =>
        rcases (rsOf_getD_iff hks).mp h with h' | h' <;> rw [hkd] at h' <;> exact nomatch h'
    rw [if_neg (by rw [hr]; exact Bool.false_ne_true), hFssD, drop_map_getD (hD.len ψ) hi]
    rw [← hnP] at hwx
    rw [denoteMeta_holeAbs_resolve hacl hfresh' (hD.opened.ord i x hx hkd) hwx, hnP,
      hD.domRead ψ i x hx, hnames, ← hk]
    rfl
  · -- a finitary field reading a member
    have hr : ((d.rss c).getD j []).getD i false = true := by
      rw [hrs]; exact (rsOf_getD_iff hks).mpr (Or.inl hkd)
    rw [if_pos hr]
    have hnone : ((d.tlss c ψ).getD j []).getD i [] = [] := by
      rw [hTl]; exact hD.tssNone ψ i (by rw [hkd]; intro h; cases h)
    rw [hnone]
    obtain ⟨hfn, htake, hlen, hres, -, -⟩ := hD.opened.recF i x hx hkd
    have ht := htgt i hi
    obtain ⟨tyt, hhole⟩ := hholes _ ht
    have hwArgs : ∀ a ∈ x.fvarTypeD.getAppArgs.drop ctx.nP, Expr.WScoped (ctx.nP + i) a := by
      intro a ha
      have hw' := hwx
      rw [← Expr.mkAppN_getApp x.fvarTypeD] at hw'
      rw [hnP]
      exact (wScoped_mkAppN _ hw').2 a (List.mem_of_mem_drop ha)
    have := denoteMeta_holeAbs_rec (holes := holes) (env := env) (φ := ψ) (ctx := ctx) hacl
      hfresh' hnd' (t := d.tgts c j i) (by rw [hnames, ← hk]; exact ht)
      (tyt := tyt) (by rw [hnP]; exact hhole) (i := i) (e := x.fvarTypeD)
      (by rw [hfn, hnames, hlps]; rfl)
      (fun p y hy => by
        rw [hnP, htake] at hy
        obtain ⟨ty, h⟩ := hD.pIdx p y hy
        exact ⟨ty, h⟩)
      (by rw [hnP, hlen]; omega) (by rw [hnP]; exact hres) hwArgs
      (by rw [hnP]; exact hD.eisRead ψ i x hx hkd)
    rw [this, hEi, hnames, ← hk, hnP]
    simp [mkPisAV, BlockData.liftTeleK]
  · -- a reflexive field reading a member
    have hr : ((d.rss c).getD j []).getD i false = true := by
      rw [hrs]; exact (rsOf_getD_iff hks).mpr (Or.inr hkd)
    rw [if_pos hr]
    obtain ⟨afvs, body, hop, htlLen, hdoms, hsp⟩ := hD.reflOpen ψ i x hx hkd
    obtain ⟨afvs', body', hop', -, hafvs, hfn, htake, hlen, hres, -, -⟩ :=
      hD.opened.reflF i x hx hkd
    rw [← htlLen] at hop'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop.symm.trans hop'))
    have ht := htgt i hi
    obtain ⟨tyt, hhole⟩ := hholes _ ht
    have hentry := hD.reflEntry ψ i hkd hi
    have hread : denoteMeta m.acval env ψ (ctx.nP + i) x.fvarTypeD
        = some (mkPisAV (d.tssF c j ψ |>.getD i [])
            (AnnotTerm.mkAppN (m.acval (d.memberName (d.tgts c j i)) ψ)
              (paramBvarsAt d.nP (d.nP + i + ((d.tssF c j ψ).getD i []).length)
                ++ (d.eissF c j ψ).getD i []))) := by
      rw [hnP, hD.domRead ψ i x hx, hentry]
    have := denoteMeta_holeAbs_refl (holes := holes) (ctx := ctx) hacl hfresh' hnd' hh
      (t := d.tgts c j i) (by rw [hnames, ← hk]; exact ht) (tyt := tyt)
      (by rw [hnP]; exact hhole) (by rw [hnP]; exact hwx) hread (by rw [hnP]; exact hop)
      hafvs (by rw [hfn, hnames, hlps]; rfl)
      (fun p y hy => by
        rw [hnP, htake] at hy
        obtain ⟨ty, h⟩ := hD.pIdx p y hy
        exact ⟨ty, h⟩)
      (by rw [hnP, hlen]; omega) (by rw [hnP]; exact hres) (by rw [hnP]; exact hsp)
    rw [this, hTl, hEi, hnames, ← hk, hnP, Nat.add_assoc (d.nP + d.k)]

/-- **A stored constructor's type, member-abstracted, reads as the hole
reading the clause records**: its fields are `absF`, its result the
component's hole at the parameters and `absE`. -/
theorem blockCtor_holeRead {c j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM c)[j]? = some cA) (hcf : BlockCtorFacts m d lps c j cA)
    {ctx : NestCtx} (hnames : ctx.names = d.memberNames) (hlps : ctx.lps = lps)
    (hnP : ctx.nP = d.nP) (hk : d.k = d.memberNames.length)
    {holes : List Expr} (hh : ∀ h ∈ holes, ∃ i ty, h = .fvar i ty)
    (hholes : ∀ t, t < d.k → ∃ ty, holes[t]? = some (.fvar (d.nP + t) ty))
    (hnd : d.memberNames.Nodup) (hfresh : ∀ n ∈ d.memberNames, d.env₀.find? n = none)
    (htgt : ∀ l, l < cA.2 → d.tgts c j l < d.k) (hc : c < d.k)
    (hwty : Expr.WScoped 0 cA.1.type) (ψ : Name → Nat) :
    ∃ (crest : Expr) (ab : List (Nat × Nat × AnnotTerm)),
      openPisAtFvars d.nP cA.1.type 0 = some (d.fvsPF c j, crest) ∧
      denoteMeta m.acval env ψ (d.nP + d.k) (holeAbs ctx holes crest)
        = some (mkPisAV ab (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
            (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      ab.map (·.2.2) = d.absF ψ c j := by
  have hcf' := hcf
  obtain ⟨-, -, hD⟩ := hcf'
  have hacl := m.acval_closed
  obtain ⟨crest, hopP, hopX⟩ := hD.opens
  have hwc : Expr.WScoped d.nP crest := by
    have := (openPisAtFvars_WScoped d.nP _ 0 hopP hwty).2
    rwa [Nat.zero_add] at this
  have hfresh' : ∀ n, n ∈ ctx.names → d.env₀.find? n = none := by rw [hnames]; exact hfresh
  have hnd' : ctx.names.Nodup := by rw [hnames]; exact hnd
  have hnF := hcf.nF hcj ψ
  -- the concrete body, peeled off the stored type's reading
  have hopAll : openPisAtFvars (d.nP + cA.2) cA.1.type 0
      = some (d.fvsPF c j ++ d.xFvsF c j, d.xrestF c j) :=
    openPisAtFvars_add d.nP hopP (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨hB, -⟩ := denoteMeta_peel (d.nP + cA.2) hopAll (hD.len ψ) (hD.read ψ)
  -- the abstract body: the component's own hole at the parameters and the indices
  obtain ⟨tyc, hholec⟩ := hholes c hc
  have hxr := hD.resShape
  have hargs : (d.xrestF c j).getAppArgs = d.fvsPF c j ++ d.idxF c j := by
    rw [hxr, Expr.getAppArgs_mkAppN]; rfl
  have hwx : Expr.WScoped (d.nP + cA.2) (d.xrestF c j) :=
    (openPisAtFvars_WScoped cA.2 crest d.nP hopX hwc).2
  have hdropI : (d.xrestF c j).getAppArgs.drop d.nP = d.idxF c j := by
    rw [hargs, List.drop_append_of_le_length (Nat.le_of_eq hD.pLen.symm), List.drop_eq_nil_of_le
      (Nat.le_of_eq hD.pLen), List.nil_append]
  have haB := denoteMeta_holeAbs_rec (holes := holes) (env := env) (φ := ψ) (ctx := ctx) hacl
    hfresh' hnd' (t := c) (by rw [hnames, ← hk]; exact hc) (tyt := tyc)
    (by rw [hnP]; exact hholec) (i := cA.2) (e := d.xrestF c j)
    (by rw [hxr, Expr.getAppFn_mkAppN, hnames, hlps]; rfl)
    (fun p y hy => by
      rw [hnP, hargs, List.take_append_of_le_length (Nat.le_of_eq hD.pLen.symm),
        List.take_of_length_le (Nat.le_of_eq hD.pLen)] at hy
      exact hD.pIdx p y hy)
    (by rw [hnP, hargs, List.length_append, hD.pLen]; omega)
    (by rw [hnP]; exact hD.opened.residRes)
    (fun a ha => by
      rw [hnP]
      rw [← Expr.mkAppN_getApp (d.xrestF c j)] at hwx
      exact (wScoped_mkAppN _ hwx).2 a (List.mem_of_mem_drop (by rwa [hnP] at ha)))
    (by rw [hnP, hdropI]; exact hD.idxRead ψ)
  -- the telescope, field by field
  obtain ⟨cg, ag, -, ha, -, hal, -, hd⟩ :=
    denoteMeta_holeAbs_tele (acval := m.acval) (env := env) (φ := ψ) (ctx := ctx) hh cA.2
      (j := 0) (by rw [hnP, Nat.add_zero]; exact hopX)
      (fun i => ((d.dsF c j ψ).getD (d.nP + i) default).2.2) (d.absField ψ c j) _ _
      (fun i x hx => by
        refine ⟨by rw [hnP, Nat.add_zero]; exact hD.domRead ψ i x hx, ?_⟩
        rw [show ctx.nP + ctx.names.length + 0 + i = d.nP + d.k + i by
          rw [hnP, hnames, ← hk, Nat.add_zero]]
        exact blockField_holeRead hcj hcf hnames hlps hnP hk hh hholes hnd hfresh htgt hwc hopX ψ hx)
      (by rw [hnP, Nat.add_zero, Nat.zero_add] at *; exact hB)
      (by rw [show ctx.nP + ctx.names.length + 0 + cA.2 = ctx.nP + ctx.names.length + cA.2 by omega];
          exact haB)
  refine ⟨crest, ag, hopP, ?_, ?_⟩
  · rw [show d.nP + d.k = ctx.nP + ctx.names.length + 0 by rw [hnP, hnames, ← hk, Nat.add_zero], ha,
      BlockData.absE, show ((d.Ess c ψ).getD j []) = d.esF c j ψ from essOfR_fixCtorDataList_getD hcj,
      hnF, hnames, ← hk, hnP]
    rfl
  · unfold BlockData.absF
    rw [hnF]
    refine List.ext_getElem (by simp [hal]) fun i h1 h2 => ?_
    have hi : i < cA.2 := by simpa using h2
    have := (hd i hi).2
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < ag.length by omega),
      Option.getD_some] at this
    simp [this]

end BlockCtor

/-! ## The walk's own term: parameters at the former's variables -/

/-- The concrete opening IS an instantiation at its variables. -/
theorem instPisWith_of_openPis :
    ∀ (n : Nat) {e : Expr} {i : Nat} {fvs : List Expr} {r : Expr},
      openPisAtFvars n e i = some (fvs, r) → instPisWith fvs e = some r
  | 0, e, i, fvs, r, h => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | n + 1, e, i, fvs, r, h => by
    match e, h with
    | .forallE dom body mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next fvs' r' hop =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show instPisWith fvs' (body.instantiate1 (.fvar i dom)) = some r'
        exact instPisWith_of_openPis n hop
      · exact nomatch h

/-- Two lists pointwise erasure-equal. -/
@[expose] def Expr.ErasedEqL : List Expr → List Expr → Prop
  | [], [] => True
  | a :: as, b :: bs => Expr.ErasedEq a b ∧ Expr.ErasedEqL as bs
  | _, _ => False

/-- Instantiation at erasure-equal arguments gives erasure-equal results. -/
theorem instPisWith_erasedEq :
    ∀ {as bs : List Expr} {e e' r : Expr}, Expr.ErasedEqL as bs →
      Expr.ErasedEq e e' → instPisWith as e = some r →
      ∃ r', instPisWith bs e' = some r' ∧ Expr.ErasedEq r r'
  | [], [], e, e', r, _, he, h => by
    simp only [instPisWith, Option.some.injEq] at h
    subst h
    exact ⟨e', rfl, he⟩
  | a :: as, b :: bs, e, e', r, ⟨hab, hrest⟩, he, h => by
    match e, e', he, h with
    | .forallE t₁ b₁ m₁, .forallE t₂ b₂ m₂, he, h =>
      obtain ⟨-, -, hb⟩ := he
      have h' : instPisWith as (b₁.instantiate1 a) = some r := h
      show ∃ r', instPisWith bs (b₂.instantiate1 b) = some r' ∧ _
      exact instPisWith_erasedEq hrest (Expr.ErasedEq.instantiate1 hb hab) h'

/-- A shift from `p` fixes a term whose variables lie below `p`. -/
theorem Expr.shiftFromN_eq_self_of_fvarsBelow {p : Nat} :
    ∀ (n : Nat) {e : Expr}, Expr.fvarsBelow p e → Expr.shiftFromN p n e = e
  | 0, _, _ => rfl
  | n + 1, e, h => by
    show Expr.shiftFrom p (Expr.shiftFromN p n e) = e
    rw [Expr.shiftFromN_eq_self_of_fvarsBelow n h, Expr.shiftFrom_eq_self h]

/-- The member abstraction commutes with instantiating a telescope. -/
theorem nestAbstract_instPisWith {ctx : NestCtx} {holes : List Expr}
    (hh : ∀ h ∈ holes, ∃ i ty, h = .fvar i ty) :
    ∀ {as : List Expr} {e r : Expr}, instPisWith as e = some r →
      instPisWith (as.map (nestAbstract ctx holes)) (nestAbstract ctx holes e)
        = some (nestAbstract ctx holes r)
  | [], e, r, h => by
    simp only [instPisWith, Option.some.injEq] at h
    subst h; rfl
  | a :: as, e, r, h => by
    match e, h with
    | .forallE t b m, h =>
      have h' : instPisWith as (b.instantiate1 a) = some r := h
      show instPisWith (as.map (nestAbstract ctx holes))
          ((nestAbstract ctx holes b).instantiate1 (nestAbstract ctx holes a)) = _
      rw [← nestAbstract_instantiate1 hh]
      exact nestAbstract_instPisWith hh h'

theorem Expr.ErasedEqL.trans : ∀ {as bs cs : List Expr}, Expr.ErasedEqL as bs →
    Expr.ErasedEqL bs cs → Expr.ErasedEqL as cs
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨Expr.ErasedEq.trans h1 h3, Expr.ErasedEqL.trans h2 h4⟩

/-- A list of variables is erasure-equal to its abstraction. -/
theorem erasedEqL_map_nestAbstract {ctx : NestCtx} {holes : List Expr} :
    ∀ {xs : List Expr}, (∀ x ∈ xs, ∃ i ty, x = .fvar i ty) →
      Expr.ErasedEqL xs (xs.map (nestAbstract ctx holes))
  | [], _ => trivial
  | x :: xs, h => by
    obtain ⟨i, ty, rfl⟩ := h x List.mem_cons_self
    exact ⟨rfl, erasedEqL_map_nestAbstract fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

section BlockCtorWalk

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {d : BlockData V}
  {lps : List Name}

/-- **THE READING THEOREM**: the term `nestPos` walks for a stored
constructor of the block — its type instantiated at the canonical
parameter variables, the members abstracted to their holes — reads, at
the walk's depth `nP + k`, as the Π-tower over the clause's fields with
holes (`absF`) ending in the component's hole at the parameters and the
clause's result index readings (`absE`). -/
theorem blockCtor_walkRead {c j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM c)[j]? = some cA) (hcf : BlockCtorFacts m d lps c j cA)
    {ctx : NestCtx} (hnames : ctx.names = d.memberNames) (hlps : ctx.lps = lps)
    (hnP : ctx.nP = d.nP) (hk : d.k = d.memberNames.length)
    (hpar : Expr.ErasedEqL ctx.params (d.fvsPF c j))
    {holes : List Expr} (hh : ∀ h ∈ holes, ∃ i ty, h = .fvar i ty)
    (hholes : ∀ t, t < d.k → ∃ ty, holes[t]? = some (.fvar (d.nP + t) ty))
    (hnd : d.memberNames.Nodup) (hfresh : ∀ n ∈ d.memberNames, d.env₀.find? n = none)
    (htgt : ∀ l, l < cA.2 → d.tgts c j l < d.k) (hc : c < d.k)
    (hwty : Expr.WScoped 0 cA.1.type) (ψ : Name → Nat)
    {crestA : Expr} (hA : instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crestA) :
    ∃ ab : List (Nat × Nat × AnnotTerm),
      denoteMeta m.acval env ψ (d.nP + d.k) crestA
        = some (mkPisAV ab (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
            (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      ab.map (·.2.2) = d.absF ψ c j := by
  obtain ⟨crest, ab, hopP, hread, hab⟩ :=
    blockCtor_holeRead hcj hcf hnames hlps hnP hk hh hholes hnd hfresh htgt hc hwty ψ
  have hcf' := hcf
  obtain ⟨-, -, hD⟩ := hcf'
  -- the concrete opening, abstracted
  have hA₂ := nestAbstract_instPisWith (ctx := ctx) hh (instPisWith_of_openPis d.nP hopP)
  have hvars : ∀ x ∈ d.fvsPF c j, ∃ i ty, x = .fvar i ty := by
    intro x hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    obtain ⟨ty, h⟩ := hD.pIdx q x hq
    exact ⟨q, ty, h⟩
  obtain ⟨crest', hc', herased⟩ :=
    instPisWith_erasedEq (hpar.trans (erasedEqL_map_nestAbstract hvars)) (Expr.ErasedEq.rfl _) hA
  rw [hA₂] at hc'
  obtain rfl := Option.some.inj hc'
  have hwc : Expr.fvarsBelow d.nP crest := by
    have := (openPisAtFvars_WScoped d.nP _ 0 hopP hwty).2
    rw [Nat.zero_add] at this
    exact this.fvarsBelow
  have hhA : holeAbs ctx holes crest = nestAbstract ctx holes crest := by
    unfold holeAbs
    rw [Expr.shiftFromN_eq_self_of_fvarsBelow _ (by rw [hnP]; exact hwc)]
  refine ⟨ab, ?_, hab⟩
  rw [← hread, hhA]
  exact denoteMeta_erasedEq herased _

end BlockCtorWalk

end ConLeche.Model
