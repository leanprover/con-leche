module

import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Verify.Inductives.ReplaceApps
public import ConLeche.Verify.Inductives.DirectGen
import ConLeche.Model.Annot.BitLemmas
public import ConLeche.Model.Annot.Bit
public section

/-!
# The walk's term and the concrete opening

Charter item 2: the clause's fields are "the interpretation of [the]
constructor types with holes at the block's members … ordinary open terms
(members abstracted to fvars)".  `nestPos` walks exactly those terms: the
stored constructor type, its parameters instantiated at the canonical
variables `0 ..< nP`, its members' WHOLE applications `T_m.{lps} p⃗`
replaced by the holes `nP ..< nP + k` (`nestCrest`), its fields opened
above the holes (`Kernel/Inductives/Positivity.lean`).

This file relates that walk to the CONCRETE opening the constructor
stage reads (parameters at `0 ..< nP`, fields at `nP ..< nP + nF`, no
holes).  The bridge is one Expr operation, `holeAbs`: the concrete term
with the fields moved `k` slots up (`Expr.shiftFromN`) and the members'
whole applications abstracted to the canonical holes (`replaceApps`,
`nestCanonSub`).  It commutes with opening a binder
(`holeAbs_instantiate1`), so the walk's telescope is the concrete one abstracted field by field, up to `fvar`
annotations (`Expr.ErasedEq`, which the reading ignores).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal NestCtx instPisWith nestCanonSub)

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

/-- **A variable replacement that only re-annotates is invisible to
erasure.** -/
theorem replaceFVars_erasedEq_idx {g : Nat → Option Expr}
    (hg : ∀ i a, g i = some a → ∃ ty, a = .fvar i ty) :
    ∀ e : Expr, Expr.ErasedEq (e.replaceFVars g) e := by
  intro e
  induction e with
  | fvar i ty _ =>
    simp only [Expr.replaceFVars]
    cases hgi : g i with
    | none => exact Expr.ErasedEq.rfl _
    | some a =>
      obtain ⟨ty', rfl⟩ := hg i a hgi
      rfl
  | app a x iha ihx => exact ⟨iha, ihx⟩
  | lam t b m iht ihb => exact ⟨rfl, iht, ihb⟩
  | forallE t b m iht ihb => exact ⟨rfl, iht, ihb⟩
  | letE t v b iht ihv ihb => exact ⟨iht, ihv, ihb⟩
  | proj s i x ih => exact ⟨rfl, rfl, ih⟩
  | bvar => exact Expr.ErasedEq.rfl _
  | sort => exact Expr.ErasedEq.rfl _
  | const => exact Expr.ErasedEq.rfl _
  | lit => exact Expr.ErasedEq.rfl _

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

theorem Expr.shiftFromN_mkAppN (p n : Nat) :
    ∀ (as : List Expr) (f : Expr),
      Expr.shiftFromN p n (Expr.mkAppN f as) = Expr.mkAppN (Expr.shiftFromN p n f)
        (as.map (Expr.shiftFromN p n))
  | [], _ => rfl
  | a :: as, f => by
    show Expr.shiftFromN p n (Expr.mkAppN (.app f a) as) = _
    rw [Expr.shiftFromN_mkAppN p n as, Expr.shiftFromN_app]
    rfl

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
members' whole applications replaced by their canonical holes. -/
@[expose] def holeAbs (ctx : NestCtx) (e : Expr) : Expr :=
  (Expr.shiftFromN ctx.nP ctx.names.length e).replaceApps
    (nestCanonSub ctx.names (ctx.lps.map .param) ctx.nP) 0 ctx.nP

theorem nestCanonSub_closed {names : List Name} {us : List Level} {n : Nat} :
    ∀ c v h, nestCanonSub names us n c v = some h → h.looseBVarsBounded 0 = true := by
  intro c v h hs
  obtain ⟨m, -, -, -, rfl⟩ := ConLeche.nestCanonSub_some hs
  rfl

/-- **The member abstraction commutes with opening a field** — the
concrete field variable at `nP + j`, the walk's at `nP + k + j`. -/
theorem holeAbs_instantiate1 {ctx : NestCtx} {j : Nat} {ty : Expr} (e : Expr) (k : Nat) :
    holeAbs ctx (e.instantiate1 (.fvar (ctx.nP + j) ty) k)
      = (holeAbs ctx e).instantiate1
          (.fvar (ctx.nP + j + ctx.names.length) (Expr.shiftFromN ctx.nP ctx.names.length ty)) k := by
  unfold holeAbs
  rw [Expr.shiftFromN_instantiate1 (Nat.le_add_right _ _),
    Expr.replaceApps_instantiate1_fvar nestCanonSub_closed (by omega)]

/-! ### `holeAbs`, structurally -/

theorem holeAbs_forallE (ctx : NestCtx) (ty body : Expr) (mb : ConLeche.BinderMeta) :
    holeAbs ctx (.forallE ty body mb) = .forallE (holeAbs ctx ty) (holeAbs ctx body) mb := by
  unfold holeAbs
  rw [Expr.shiftFromN_forallE]
  rfl

/-- A field variable moves above the holes. -/
theorem holeAbs_fvar_ge (ctx : NestCtx) {i : Nat} (hi : ctx.nP ≤ i) (ty : Expr) :
    holeAbs ctx (.fvar i ty)
      = .fvar (i + ctx.names.length) (Expr.shiftFromN ctx.nP ctx.names.length ty) := by
  unfold holeAbs
  rw [Expr.shiftFromN_fvar_ge' hi]
  rfl

/-- A parameter variable stays (its annotation abstracted). -/
theorem holeAbs_fvar_lt (ctx : NestCtx) {i : Nat} (hi : i < ctx.nP) (ty : Expr) :
    ∃ ty', holeAbs ctx (.fvar i ty) = .fvar i ty' := by
  obtain ⟨ty', h⟩ := Expr.shiftFromN_fvar ctx.nP ctx.names.length i ty
  rw [if_pos hi] at h
  unfold holeAbs
  rw [h]
  exact ⟨_, rfl⟩

/-! ## The walk's opening IS the concrete one, abstracted -/

/-- **Opening the abstracted telescope** (or any term erasure-equal to
it) at the walk's depth gives, up to erasure, the abstracted body of the
concrete opening (the opened variables' annotations are the concrete
ones shifted, the abstraction does not descend into them). -/
theorem openPisAtFvars_holeAbs {ctx : NestCtx} :
    ∀ (n : Nat) {e : Expr} {j : Nat} {xs : List Expr} {rest : Expr} {e' : Expr},
      openPisAtFvars n e (ctx.nP + j) = some (xs, rest) → Expr.ErasedEq e' (holeAbs ctx e) →
      ∃ xs' rest', openPisAtFvars n e' (ctx.nP + ctx.names.length + j) = some (xs', rest') ∧
        Expr.ErasedEq rest' (holeAbs ctx rest)
  | 0, e, j, xs, rest, e', h, he => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, ⟨rfl, rfl⟩, he⟩
  | n + 1, e, j, xs, rest, e', h, he => by
    match e, h with
    | .forallE dom body mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next fvs r hop =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [holeAbs_forallE] at he
        cases e' with
        | forallE dom' body' mb' =>
          obtain ⟨-, -, hb⟩ := he
          have hop' : openPisAtFvars n (body.instantiate1 (.fvar (ctx.nP + j) dom))
              (ctx.nP + (j + 1)) = some (fvs, r) := by rw [← Nat.add_assoc]; exact hop
          have hb' : Expr.ErasedEq
              (body'.instantiate1 (.fvar (ctx.nP + ctx.names.length + j) dom') 0)
              (holeAbs ctx (body.instantiate1 (.fvar (ctx.nP + j) dom) 0)) := by
            rw [holeAbs_instantiate1 body 0]
            exact Expr.ErasedEq.instantiate1 (v := .fvar _ dom') (v' := .fvar _ _) hb
              (by show ctx.nP + ctx.names.length + j = ctx.nP + j + ctx.names.length; omega)
          obtain ⟨xs', rest', hop'', hr⟩ := openPisAtFvars_holeAbs n hop' hb'
          refine ⟨.fvar (ctx.nP + ctx.names.length + j) dom' :: xs', rest', ?_, hr⟩
          simp only [openPisAtFvars]
          rw [show ctx.nP + ctx.names.length + j + 1 = ctx.nP + ctx.names.length + (j + 1) by omega,
            hop'']
        | _ => simp [Expr.ErasedEq] at he
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

/-- A constant applied to exactly the canonical parameter variables is a
placeholder spine. -/
theorem phApp?_mkAppN_params {b : Nat} {c : Name} {v : List Level} :
    ∀ (n : Nat) (args : List Expr), args.length = n →
      (∀ p x, args[p]? = some x → ∃ ty, x = Expr.fvar (b + p) ty) →
      (Expr.mkAppN (.const c v) args).phApp? b n = some (c, v)
  | 0, args, hl, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    rfl
  | n + 1, args, hl, hx => by
    rcases List.eq_nil_or_concat args with rfl | ⟨pre, y, rfl⟩
    · simp at hl
    · rw [List.concat_eq_append] at hl hx ⊢
      simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
      obtain ⟨ty, rfl⟩ := hx pre.length y (by simp)
      rw [Expr.mkAppN_append_one]
      simp only [Expr.phApp?, hl, if_true]
      exact phApp?_mkAppN_params n pre hl fun p x hp =>
        hx p x (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hp).1]; exact hp)

/-- **The abstraction of a member applied to the parameters** is the
member's canonical hole, applied to the rest abstracted. -/
theorem holeAbs_memberApp {ctx : NestCtx} (hnd : ctx.names.Nodup) {t : Nat}
    (ht : t < ctx.names.length) {fvsP : List Expr} (hlen : fvsP.length = ctx.nP)
    (hvar : ∀ p x, fvsP[p]? = some x → ∃ ty, x = Expr.fvar p ty) (rest : List Expr) :
    holeAbs ctx (Expr.mkAppN (.const (ctx.names.getD t .anonymous) (ctx.lps.map .param))
        (fvsP ++ rest))
      = Expr.mkAppN (.fvar (ctx.nP + t) (.sort .zero)) (rest.map (holeAbs ctx)) := by
  unfold holeAbs
  rw [Expr.shiftFromN_mkAppN, Expr.shiftFromN_const, List.map_append]
  have hnm : nestCanonSub ctx.names (ctx.lps.map .param) ctx.nP (ctx.names.getD t .anonymous)
      (ctx.lps.map .param) = some (.fvar (ctx.nP + t) (.sort .zero)) := by
    simp only [ConLeche.nestCanonSub, beq_self_eq_true, if_true, findIdx?_beq_of_nodup hnd ht,
      Option.map_some]
  rw [Expr.replaceApps_mkAppN_hit hnm (phApp?_mkAppN_params ctx.nP _ (by simp [hlen])
    (fun p x hx => ?_)), List.map_map]
  · rfl
  · rw [List.getElem?_map] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨ty, rfl⟩ := hvar p y hy
    have hp : p < ctx.nP := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hy).1
    obtain ⟨ty', h⟩ := Expr.shiftFromN_fvar ctx.nP ctx.names.length p ty
    rw [if_pos hp] at h
    exact ⟨ty', by rw [h, Nat.zero_add]⟩

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

theorem Expr.ErasedEqL.trans : ∀ {as bs cs : List Expr}, Expr.ErasedEqL as bs →
    Expr.ErasedEqL bs cs → Expr.ErasedEqL as cs
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨Expr.ErasedEq.trans h1 h3, Expr.ErasedEqL.trans h2 h4⟩

end ConLeche.Model
