module

public import ConLeche.Verify.Inductives.NestedRestoreOpen
import ConLeche.Verify.Inductives.NestedCopyTele
import ConLeche.Verify.Subst
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Level

public section

/-!
# The copy constructor, instantiated (task #315 L-B, DESIGN §U.23)

`mkCopy` (`ConLeche/Kernel/Inductives/NestedElim.lean`) stores a copy's
constructor as `closeTelescope pbs 0 cI` with

    cI = Expr.instPis (Expr.instantiateLevelParams J.lps lvls cc.type) Ds

— the container constructor's type, its level parameters replaced by
the occurrence's levels, its parameter telescope instantiated at the
pin's arguments `Ds`.  This module is the *syntactic* half of reading
that term: what `instPis` at a `∀`-telescope is (`instPis_mkPisB`),
how the resulting `instSeq` walks through a telescope
(`instSeq_mkPisB`, with the per-binder cuts collected in
`instTeleSeq`), what it does to the closed spellings a constructor
type is built from (`instSeq_const`, `instSeq_mkAppN_const`,
`instSeq_structPsAt`, `instSeq_bvar_below`), and how the level
substitution commutes with all of it (`ilp_*`).

Two orders meet in `instPis_mkPisB` and have to be kept apart:
`instPis` instantiates the OUTERMOST binder, at cut `0`, of a body
that still carries the remaining binders, while `Expr.instSeq as n`
instantiates the fully stripped body at the descending cuts
`n, n-1, …, 0` — the outermost parameter is the HIGHEST bvar there.
`mkPisB_instantiate1` is what turns the first into the second: pushing
one `instantiate1` under the remaining `k` binders raises its cut to
`k`.
-/

namespace ConLeche

open Expr

/-! ## `instPis` at a telescope -/

/-- **`instPis` at a `∀`-telescope is `instSeq` at its body**: the
`instPis` walk instantiates the outermost binder at cut `0` of a body
that still carries the remaining `k` binders, which `instTeleB`/
`mkPisB_instantiate1` turn into an instantiation of the stripped body
at cut `k` — the descending cuts of `Expr.instSeq as (as.length - 1)`. -/
theorem instPis_mkPisB :
    ∀ (ps : List (Expr × BinderMeta)) (as : List Expr) (body : Expr),
      ps.length = as.length →
      Expr.instPis (mkPisB ps body) as
        = some (Expr.instSeq as (as.length - 1) body) := by
  have key : ∀ (as : List Expr) (ps : List (Expr × BinderMeta)) (body : Expr),
      ps.length = as.length →
      Expr.instPis (mkPisB ps body) as
        = some (Expr.instSeq as (as.length - 1) body) := by
    intro as
    induction as with
    | nil =>
      intro ps body h
      obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero h
      rw [mkPisB_nil]
      rfl
    | cons a as ih =>
      intro ps body h
      cases ps with
      | nil => simp at h
      | cons p ps =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h
        rw [mkPisB_cons]
        show Expr.instPis ((mkPisB ps body).instantiate1 a 0) as = _
        rw [mkPisB_instantiate1,
          ih (instTeleB a 0 ps) _ (by rw [instTeleB_length]; exact h)]
        simp only [List.length_cons, Nat.add_sub_cancel, Nat.zero_add, h]
        rfl
  intro ps as body h
  exact key as ps body h

/-! ## `instSeq` through a telescope -/

/-- The binder domains of a telescope under an instantiation sequence:
the entry at position `l` (outermost first) sits under `l` extra
binders, so it is instantiated at the cuts starting from `t + l`. -/
@[expose] def instTeleSeq (as : List Expr) :
    Nat → List (Expr × BinderMeta) → List (Expr × BinderMeta)
  | _, [] => []
  | t, b :: bs => (Expr.instSeq as t b.1, b.2) :: instTeleSeq as (t + 1) bs

/-- `instTeleSeq` keeps the telescope's length. -/
theorem instTeleSeq_length (as : List Expr) :
    ∀ (t : Nat) (bs : List (Expr × BinderMeta)),
      (instTeleSeq as t bs).length = bs.length
  | _, [] => rfl
  | t, b :: bs => by
    show (instTeleSeq as (t + 1) bs).length + 1 = bs.length + 1
    rw [instTeleSeq_length as (t + 1) bs]

/-- `instTeleSeq` entrywise: the `l`-th domain, instantiated at the
cuts from `t + l`. -/
theorem instTeleSeq_getD (as : List Expr) :
    ∀ (bs : List (Expr × BinderMeta)) (t l : Nat), l < bs.length →
      (instTeleSeq as t bs).getD l default
        = (Expr.instSeq as (t + l) (bs.getD l default).1,
            (bs.getD l default).2) := by
  intro bs
  induction bs with
  | nil => intro t l h; simp at h
  | cons b bs ih =>
    intro t l h
    cases l with
    | zero => simp [instTeleSeq]
    | succ l =>
      simp only [List.length_cons] at h
      simp only [instTeleSeq, List.getD_cons_succ]
      rw [ih (t + 1) l (by omega), show t + 1 + l = t + (l + 1) from by omega]

/-- **An instantiation sequence walks a `∀`-telescope**: each domain is
instantiated at its own cut (`instTeleSeq`), the result at the cut
below the whole telescope.  The side condition is the one
`Expr.instSeq_forallE` needs — an argument list no longer than the cut
allows, which is how every consumer instantiates (`as.length = t + 1`). -/
theorem instSeq_mkPisB (as : List Expr) :
    ∀ (t : Nat) (bs : List (Expr × BinderMeta)) (res : Expr), as.length ≤ t + 1 →
      Expr.instSeq as t (mkPisB bs res)
        = mkPisB (instTeleSeq as t bs) (Expr.instSeq as (t + bs.length) res)
  | t, [], res, _ => by
    rw [mkPisB_nil]
    show _ = mkPisB (instTeleSeq as t []) (Expr.instSeq as (t + 0) res)
    rw [show instTeleSeq as t [] = [] from rfl, mkPisB_nil, Nat.add_zero]
  | t, b :: bs, res, h => by
    rw [mkPisB_cons, Expr.instSeq_forallE as t _ _ _ h,
      instSeq_mkPisB as (t + 1) bs res (by omega)]
    show _ = mkPisB ((Expr.instSeq as t b.1, b.2) :: instTeleSeq as (t + 1) bs)
      (Expr.instSeq as (t + (bs.length + 1)) res)
    rw [mkPisB_cons, show t + (bs.length + 1) = t + 1 + bs.length from by omega]

/-! ## The closed spellings under an instantiation sequence -/

/-- A constant is untouched. -/
theorem instSeq_const (as : List Expr) (t : Nat) (c : Name) (us : List Level) :
    Expr.instSeq as t (.const c us) = .const c us :=
  Expr.instSeq_eq_self as t rfl

/-- A constant-headed application spine: the head stays, the arguments
are instantiated. -/
theorem instSeq_mkAppN_const (as : List Expr) (t : Nat) (c : Name)
    (us : List Level) (args : List Expr) :
    Expr.instSeq as t (Expr.mkAppN (.const c us) args)
      = Expr.mkAppN (.const c us) (args.map (Expr.instSeq as t)) := by
  rw [Expr.instSeq_mkAppN, instSeq_const]

/-- A bound variable below every cut of the sequence is untouched. -/
theorem instSeq_bvar_below :
    ∀ (as : List Expr) (t i : Nat), i + as.length ≤ t →
      Expr.instSeq as t (.bvar i) = .bvar i
  | [], _, _, _ => rfl
  | a :: as, t, i, h => by
    simp only [List.length_cons] at h
    show Expr.instSeq as (t - 1) ((Expr.bvar i).instantiate1 a t) = _
    rw [show (Expr.bvar i).instantiate1 a t = Expr.bvar i from by
      simp only [Expr.instantiate1]
      rw [if_neg (by omega : ¬ i = t), if_neg (by omega : ¬ i > t)]]
    exact instSeq_bvar_below as (t - 1) i (by omega)

/-- **The parameter spine is eaten by the pin's arguments**: the spine
`p⃗` as seen from under `l` binders, instantiated at the closed
arguments `Ds` at the telescope's own cut, IS `Ds`. -/
theorem instSeq_structPsAt (Ds : List Expr) (l : Nat)
    (hcl : ∀ a ∈ Ds, a.looseBVarsBounded 0 = true) :
    (structPsAt l Ds.length).map (Expr.instSeq Ds (l + Ds.length - 1)) = Ds := by
  apply List.ext_getElem
  · simp [structPsAt]
  · intro k h1 _
    have hk : k < Ds.length := by simpa [structPsAt] using h1
    simp only [structPsAt, List.getElem_map, List.getElem_range]
    have hhit := Expr.instSeq_bvar Ds (l + Ds.length - 1) (l + Ds.length - 1 - k)
      hcl (by omega) (by omega)
    rw [show l + Ds.length - 1 - (l + Ds.length - 1 - k) = k from by omega,
      List.getElem?_eq_getElem (by omega)] at hhit
    exact (Option.some.inj hhit).symm

/-! ## Level instantiation -/

/-- Level instantiation walks a `∀`-telescope: the domains and the body
instantiated, each binder's prop-ness datum substituted. -/
theorem ilp_mkPisB (ks : List Name) (us : List Level) :
    ∀ (bs : List (Expr × BinderMeta)) (res : Expr),
      Expr.instantiateLevelParams ks us (mkPisB bs res)
        = mkPisB (bs.map fun b =>
            (Expr.instantiateLevelParams ks us b.1,
              (⟨Level.substPW ks us b.2.pw⟩ : BinderMeta)))
          (Expr.instantiateLevelParams ks us res)
  | [], res => by
    rw [mkPisB_nil, List.map_nil, mkPisB_nil]
  | b :: bs, res => by
    rw [mkPisB_cons, List.map_cons, mkPisB_cons]
    show Expr.forallE (Expr.instantiateLevelParams ks us b.1)
        (Expr.instantiateLevelParams ks us (mkPisB bs res))
        ⟨Level.substPW ks us b.2.pw⟩ = _
    rw [ilp_mkPisB ks us bs res]

/-- Level instantiation distributes over an application spine (the
existing `Expr.instantiateLevelParams_mkAppN`, under this file's
name). -/
theorem ilp_mkAppN (ks : List Name) (us : List Level) (f : Expr) (args : List Expr) :
    Expr.instantiateLevelParams ks us (Expr.mkAppN f args)
      = Expr.mkAppN (Expr.instantiateLevelParams ks us f)
          (args.map (Expr.instantiateLevelParams ks us)) :=
  instantiateLevelParams_mkAppN ks us args f

/-- Substituting a duplicate-free parameter list's own parameters
yields the values, in order. -/
theorem Level.subst_map_params :
    ∀ (ks : List Name) (us : List Level), ks.Nodup → ks.length = us.length →
      (ks.map Level.param).map (Level.subst ks us) = us := by
  intro ks
  induction ks with
  | nil =>
    intro us _ hl
    cases us with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons k ks ih =>
    intro us hnd hl
    cases us with
    | nil => simp at hl
    | cons u us =>
      have hne : ∀ n ∈ ks, ¬ k = n := by
        intro n hn h
        exact absurd (h ▸ hn) (List.nodup_cons.mp hnd).1
      have htail : ∀ l : List Name, (∀ n ∈ l, ¬ k = n) →
          (l.map Level.param).map (Level.subst (k :: ks) (u :: us))
            = (l.map Level.param).map (Level.subst ks us) := by
        intro l
        induction l with
        | nil => intro _; rfl
        | cons n l ihl =>
          intro hall
          simp only [List.map_cons,
            ihl (fun m hm => hall m (List.mem_cons_of_mem _ hm))]
          congr 1
          show Level.subst.go (k :: ks) (u :: us) n = Level.subst.go ks us n
          simp only [Level.subst.go, if_neg (hall n List.mem_cons_self)]
      simp only [List.map_cons, htail ks hne,
        ih us (List.nodup_cons.mp hnd).2 (by simpa using hl)]
      congr 1
      show Level.subst.go (k :: ks) (u :: us) k = u
      simp [Level.subst.go]

/-- **A constant at its own parameters instantiates to the values**:
the shape `mkCopy` substitutes into (`J.lps` are the container's level
parameters, `lvls` the occurrence's levels). -/
theorem ilp_const_params (ks : List Name) (us : List Level) (c : Name)
    (hnd : ks.Nodup) (hl : ks.length = us.length) :
    Expr.instantiateLevelParams ks us (.const c (ks.map Level.param))
      = .const c us := by
  show Expr.const c ((ks.map Level.param).map (Level.subst ks us)) = _
  rw [Level.subst_map_params ks us hnd hl]

/-- Level instantiation leaves a parameter spine alone. -/
theorem ilp_structPsAt (ks : List Name) (us : List Level) (o n : Nat) :
    (structPsAt o n).map (Expr.instantiateLevelParams ks us) = structPsAt o n := by
  simp [structPsAt, List.map_map, Function.comp_def, Expr.instantiateLevelParams]

/-- Level instantiation commutes with binder opening, at an arbitrary
argument (`Expr.instantiateLevelParams_instantiate1` is the `fvar`
case). -/
theorem ilp_instantiate1 (ks : List Name) (us : List Level) {v : Expr} :
    ∀ (e : Expr) (k : Nat),
      Expr.instantiateLevelParams ks us (e.instantiate1 v k)
        = (Expr.instantiateLevelParams ks us e).instantiate1
            (Expr.instantiateLevelParams ks us v) k := by
  intro e
  induction e <;> intro k <;>
    simp_all [Expr.instantiate1, Expr.instantiateLevelParams]
  case bvar i =>
    split
    · rfl
    · split <;> simp [Expr.instantiateLevelParams]

/-- Level instantiation commutes with an instantiation sequence (the
arguments instantiated too). -/
theorem ilp_instSeq (ks : List Name) (us : List Level) :
    ∀ (as : List Expr) (t : Nat) (e : Expr),
      Expr.instantiateLevelParams ks us (Expr.instSeq as t e)
        = Expr.instSeq (as.map (Expr.instantiateLevelParams ks us)) t
            (Expr.instantiateLevelParams ks us e)
  | [], _, _ => rfl
  | a :: as, t, e => by
    show Expr.instantiateLevelParams ks us
      (Expr.instSeq as (t - 1) (e.instantiate1 a t)) = _
    rw [ilp_instSeq ks us as (t - 1) (e.instantiate1 a t), ilp_instantiate1]
    rfl

/-! ## Telescope bookkeeping -/

/-- A telescope is stripped back to its own binders. -/
theorem stripPis_mkPisB_self :
    ∀ (bs : List (Expr × BinderMeta)) (res : Expr),
      (mkPisB bs res).stripPis bs.length = some (bs, res)
  | [], res => by rw [mkPisB_nil]; rfl
  | b :: bs, res => by
    rw [mkPisB_cons]
    simp only [List.length_cons, Expr.stripPis, stripPis_mkPisB_self bs res,
      Option.map_some]

/-- A telescope over an append is the telescopes nested. -/
theorem mkPisB_append :
    ∀ (bs₁ bs₂ : List (Expr × BinderMeta)) (res : Expr),
      mkPisB (bs₁ ++ bs₂) res = mkPisB bs₁ (mkPisB bs₂ res)
  | [], bs₂, res => by rw [List.nil_append, mkPisB_nil]
  | b :: bs₁, bs₂, res => by
    rw [List.cons_append, mkPisB_cons, mkPisB_cons, mkPisB_append bs₁ bs₂ res]

/-- **Each instantiation eats one cut**: a body bounded at `t + 1`,
instantiated at `k ≤ t + 1` closed arguments from cut `t` down, is
bounded at `t + 1 - k`. -/
theorem looseBVarsBounded_instSeq_gen :
    ∀ (as : List Expr) (t : Nat) (e : Expr),
      (∀ a ∈ as, a.looseBVarsBounded 0 = true) →
      e.looseBVarsBounded (t + 1) = true → as.length ≤ t + 1 →
      (Expr.instSeq as t e).looseBVarsBounded (t + 1 - as.length) = true
  | [], _, _, _, he, _ => he
  | a :: as, t, e, hcl, he, hlen => by
    have he' : (e.instantiate1 a t).looseBVarsBounded t = true :=
      looseBVarsBounded_instantiate1_gen (hcl a List.mem_cons_self) he
    simp only [List.length_cons] at hlen
    cases t with
    | zero =>
      obtain rfl : as = [] := by
        cases as with
        | nil => rfl
        | cons _ _ => simp at hlen
      show (e.instantiate1 a 0).looseBVarsBounded (0 + 1 - 1) = true
      simpa using he'
    | succ t' =>
      show (Expr.instSeq as (t' + 1 - 1)
        (e.instantiate1 a (t' + 1))).looseBVarsBounded _ = true
      have hrec := looseBVarsBounded_instSeq_gen as t' (e.instantiate1 a (t' + 1))
        (fun x hx => hcl x (List.mem_cons_of_mem _ hx)) (by simpa using he')
        (by omega)
      rw [show t' + 1 - 1 = t' from rfl, List.length_cons,
        show t' + 1 + 1 - (as.length + 1) = t' + 1 - as.length from by omega]
      exact hrec

/-- The closed instantiation: a full argument list closes the body. -/
theorem looseBVarsBounded_instSeq (as : List Expr) (t : Nat) (e : Expr)
    (hcl : ∀ a ∈ as, a.looseBVarsBounded 0 = true)
    (he : e.looseBVarsBounded (t + 1) = true) (hlen : as.length = t + 1) :
    (Expr.instSeq as t e).looseBVarsBounded 0 = true := by
  have h := looseBVarsBounded_instSeq_gen as t e hcl he (by omega)
  rwa [hlen, Nat.sub_self] at h

/-! ## The copy's constructor telescope, in one step (task #315 L-B) -/

/-- **`mkCopy`'s constructor body, as a telescope**: the container
constructor's type is a `∀`-tower over its parameters `pcs` and its
fields `fcs`; `mkCopy` substitutes the occurrence's levels and
instantiates the parameters at the pin's components, which leaves the
FIELDS' tower with each domain instantiated at the descending cuts
from `|Ds| - 1` and the residual at `|Ds| - 1 + |fcs|`. -/
theorem instPis_ilp_mkPisB (ks : List Name) (us : List Level) (Ds : List Expr)
    (pcs fcs : List (Expr × BinderMeta)) (res : Expr) (hlen : pcs.length = Ds.length) :
    Expr.instPis (Expr.instantiateLevelParams ks us (mkPisB (pcs ++ fcs) res)) Ds
      = some (mkPisB (instTeleSeq Ds (Ds.length - 1) (fcs.map fun b =>
            (Expr.instantiateLevelParams ks us b.1,
              (⟨Level.substPW ks us b.2.pw⟩ : BinderMeta))))
          (Expr.instSeq Ds (Ds.length - 1 + fcs.length)
            (Expr.instantiateLevelParams ks us res))) := by
  rw [ilp_mkPisB, List.map_append, mkPisB_append,
    instPis_mkPisB _ Ds _ (by rw [List.length_map]; exact hlen),
    instSeq_mkPisB Ds (Ds.length - 1) _ _ (by omega), List.length_map]

end ConLeche
