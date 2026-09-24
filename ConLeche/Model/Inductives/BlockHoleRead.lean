module

import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Verify.Inductives.FixRec
import ConLeche.Model.Annot.BitLemmas
public import ConLeche.Model.Annot.Bit
public section

/-!
# The walk's term and the concrete opening (lane HOLE2)

Charter item 2: the clause's fields are "the interpretation of [the]
constructor types with holes at the block's members … ordinary open terms
(members abstracted to fvars)".  `nestPos` walks exactly those terms: the
stored constructor type, its parameters instantiated at the canonical
variables `0 ..< nP`, its members' constants replaced by the holes
`nP ..< nP + k` (`nestAbstract`), its fields opened above the holes
(`Kernel/Inductives/Positivity.lean`).

This file relates that walk to the CONCRETE opening the constructor stage
reads (parameters at `0 ..< nP`, fields at `nP ..< nP + nF`, no holes).  The bridge is one Expr operation,
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

/-- Replacing constants by erasure-equal replacements keeps
erasure-equality. -/
theorem Expr.ErasedEq.replaceConsts {f g : Name → List Level → Option Expr}
    (hfg : ∀ c us, (f c us = none ∧ g c us = none) ∨
      ∃ a b, f c us = some a ∧ g c us = some b ∧ Expr.ErasedEq a b) :
    ∀ {a b : Expr}, Expr.ErasedEq a b → Expr.ErasedEq (a.replaceConsts f) (b.replaceConsts g)
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
      simp only [Expr.replaceConsts]
      rcases hfg n us with ⟨h1, h2⟩ | ⟨a, b, h1, h2, h3⟩
      · rw [h1, h2]; exact Expr.ErasedEq.rfl _
      · rw [h1, h2]; exact h3
  | .app f₁ a₁, b, h => by
    match b, h with
    | .app f₂ a₂, h =>
      exact ⟨Expr.ErasedEq.replaceConsts hfg h.1, Expr.ErasedEq.replaceConsts hfg h.2⟩
  | .lam t₁ b₁ m₁, b, h => by
    match b, h with
    | .lam t₂ b₂ m₂, h =>
      exact ⟨h.1, Expr.ErasedEq.replaceConsts hfg h.2.1, Expr.ErasedEq.replaceConsts hfg h.2.2⟩
  | .forallE t₁ b₁ m₁, b, h => by
    match b, h with
    | .forallE t₂ b₂ m₂, h =>
      exact ⟨h.1, Expr.ErasedEq.replaceConsts hfg h.2.1, Expr.ErasedEq.replaceConsts hfg h.2.2⟩
  | .letE t₁ v₁ b₁, b, h => by
    match b, h with
    | .letE t₂ v₂ b₂, h =>
      exact ⟨Expr.ErasedEq.replaceConsts hfg h.1, Expr.ErasedEq.replaceConsts hfg h.2.1,
        Expr.ErasedEq.replaceConsts hfg h.2.2⟩
  | .lit l, b, h => by
    match b, h with
    | .lit l', h => exact h
  | .proj s i e, b, h => by
    match b, h with
    | .proj s' i' e', h => exact ⟨h.1, h.2.1, Expr.ErasedEq.replaceConsts hfg h.2.2⟩

/-- Two lists pointwise erasure-equal. -/
@[expose] def Expr.ErasedEqL : List Expr → List Expr → Prop
  | [], [] => True
  | a :: as, b :: bs => Expr.ErasedEq a b ∧ Expr.ErasedEqL as bs
  | _, _ => False

/-- Two lists of variables at the same consecutive indices are
erasure-equal. -/
theorem erasedEqL_of_fvarIdx :
    ∀ (as bs : List Expr) (o : Nat),
      (∀ (i : Nat) (x : Expr), as[i]? = some x → ∃ ty, x = .fvar (o + i) ty) →
      (∀ (i : Nat) (x : Expr), bs[i]? = some x → ∃ ty, x = .fvar (o + i) ty) →
      as.length = bs.length → Expr.ErasedEqL as bs
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | a :: as, b :: bs, o, ha, hb, h => by
    obtain ⟨ta, rfl⟩ := ha 0 a rfl
    obtain ⟨tb, rfl⟩ := hb 0 b rfl
    refine ⟨rfl, erasedEqL_of_fvarIdx as bs (o + 1) (fun i x hx => ?_) (fun i x hx => ?_)
      (by simpa using h)⟩
    · obtain ⟨ty, hty⟩ := ha (i + 1) x hx
      exact ⟨ty, by rw [hty]; congr 1; omega⟩
    · obtain ⟨ty, hty⟩ := hb (i + 1) x hx
      exact ⟨ty, by rw [hty]; congr 1; omega⟩

/-- Erasure-equal lists agree position by position. -/
theorem Expr.ErasedEqL.getElem? : ∀ {as bs : List Expr}, Expr.ErasedEqL as bs → ∀ i : Nat,
    (as[i]? = none ∧ bs[i]? = none) ∨ ∃ a b, as[i]? = some a ∧ bs[i]? = some b ∧ Expr.ErasedEq a b
  | [], [], _, _ => Or.inl ⟨rfl, rfl⟩
  | a :: _, b :: _, ⟨h, _⟩, 0 => Or.inr ⟨a, b, rfl, rfl, h⟩
  | _ :: _, _ :: _, ⟨_, h⟩, i + 1 => by
    simpa using Expr.ErasedEqL.getElem? h i

/-- **The member abstraction is blind to the holes' annotations** (up to
erasure): at the same names and levels, erasure-equal holes give
erasure-equal abstractions. -/
theorem nestAbstract_erasedEq {ctx ctx' : NestCtx} {holes holes' : List Expr}
    (hn : ctx.names = ctx'.names) (hl : ctx.lps = ctx'.lps) (hh : Expr.ErasedEqL holes holes')
    (e : Expr) : Expr.ErasedEq (nestAbstract ctx holes e) (nestAbstract ctx' holes' e) := by
  refine Expr.ErasedEq.replaceConsts (fun c us => ?_) (Expr.ErasedEq.rfl e)
  rw [← hn, ← hl]
  split
  · split
    · exact hh.getElem? _
    · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

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


end ConLeche.Model
