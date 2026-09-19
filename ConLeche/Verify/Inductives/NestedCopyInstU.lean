module

public import ConLeche.Verify.Inductives.NestedRestoreOpen
import ConLeche.Verify.AbstractRange
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

/-! ## Reading a parameter spine back (task #315 L-B) -/

/-- A FULL instantiation sequence (`|as| = t + 1`) turns a bound
variable above its top cut into a bound variable again: the lowering
steps stay ahead of the arguments, so nothing in `as` is ever reached.
Together with `Expr.instSeq_bvar` this is the complete case split on
what a sequence does to a `bvar`. -/
private theorem instSeq_bvar_above :
    ∀ (as : List Expr) (t j : Nat), as.length = t + 1 → t < j →
      ∃ j', Expr.instSeq as t (.bvar j) = .bvar j'
  | [], _, _, hlen, _ => by simp at hlen
  | a :: as, t, j, hlen, hj => by
    show ∃ j', Expr.instSeq as (t - 1) ((Expr.bvar j).instantiate1 a t) = _
    rw [show (Expr.bvar j).instantiate1 a t = Expr.bvar (j - 1) from by
      simp only [Expr.instantiate1]
      rw [if_neg (by omega : ¬ j = t), if_pos (by omega : j > t)]]
    cases t with
    | zero =>
      obtain rfl : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      exact ⟨j - 1, rfl⟩
    | succ t' =>
      exact instSeq_bvar_above as t' (j - 1) (by simpa using hlen) (by omega)

/-- An instantiation sequence can only produce an `fvar` out of an
`fvar` or out of a bound variable: `Expr.instantiate1` preserves every
other constructor, so the head it started from is the head it ends
with. -/
private theorem instSeq_fvar_cases :
    ∀ (as : List Expr) (t : Nat) (e : Expr) (i : Nat) (ty : Expr),
      Expr.instSeq as t e = .fvar i ty →
      (∃ j, e = .bvar j) ∨ (∃ ty', e = .fvar i ty')
  | [], _, e, _, ty, h => Or.inr ⟨ty, h⟩
  | a :: as, t, e, i, ty, h => by
    have h' : Expr.instSeq as (t - 1) (e.instantiate1 a t) = Expr.fvar i ty := h
    have ih := instSeq_fvar_cases as (t - 1) (e.instantiate1 a t) i ty h'
    cases e with
    | bvar j => exact Or.inl ⟨j, rfl⟩
    | fvar i' ty' =>
      refine Or.inr ⟨ty', ?_⟩
      rcases ih with ⟨j, hj⟩ | ⟨ty'', hj⟩ <;>
        simp only [Expr.instantiate1] at hj
      · exact absurd hj (by simp)
      · rw [(Expr.fvar.inj hj).1]
    | _ =>
      rcases ih with ⟨j, hj⟩ | ⟨ty'', hj⟩ <;>
        simp only [Expr.instantiate1] at hj <;> exact Expr.noConfusion hj

/-- **The converse of `instSeq_structPsAt`**: a CLOSED parameter spine
that instantiates to the telescope's own parameter openers WAS the
canonical `structPsAt` spine.  A stored constructor field's domain is
an application `mkAppN (.const T us) (pargs ++ is)` with `pargs`
fvar-free; once the domain has been opened at the block's telescope and
its first `nP` arguments read off as the parameter openers `fvsP`
(indices `0 … nP-1`, the remaining openers `rest` all above `nP`), this
identifies `pargs` syntactically — which is what lets the caller
re-instantiate the same spine at a pin's components with
`instSeq_structPsAt`. -/
theorem structPsAt_of_instSeq_fvsP (nP l : Nat) (fvsP rest pargs : List Expr)
    (hlenP : fvsP.length = nP)
    (hfvsP : ∀ k, k < nP → ∃ ty, fvsP[k]? = some (Expr.fvar k ty))
    (hrest : ∀ a ∈ rest, ∃ (j : Nat) (ty : Expr), a = Expr.fvar j ty ∧ nP ≤ j)
    (hlenR : rest.length = l)
    (hcl : ∀ a ∈ pargs, a.hasFvar = false)
    (hlen : pargs.length = nP)
    (hmap : pargs.map (Expr.instSeq (fvsP ++ rest) (nP + l - 1)) = fvsP) :
    pargs = structPsAt l nP := by
  have hvslen : (fvsP ++ rest).length = nP + l := by
    rw [List.length_append, hlenP, hlenR]
  have hclvs : ∀ a ∈ fvsP ++ rest, a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp ha
      obtain ⟨ty2, hty2⟩ := hfvsP m (by omega)
      rw [List.getElem?_eq_getElem hm] at hty2
      rw [Option.some.inj hty2]
      rfl
    · obtain ⟨j, ty2, rfl, _⟩ := hrest a ha
      rfl
  apply List.ext_getElem
  · simp [structPsAt, hlen]
  · intro k h1 _
    have hk : k < nP := by omega
    obtain ⟨ty, hty⟩ := hfvsP k hk
    -- the `k`-th entry instantiates to the `k`-th opener
    have hfk : Expr.instSeq (fvsP ++ rest) (nP + l - 1) pargs[k] = Expr.fvar k ty := by
      have hc := congrArg (fun L => L[k]?) hmap
      simp only [List.getElem?_map, List.getElem?_eq_getElem h1,
        Option.map_some, hty] at hc
      exact Option.some.inj hc
    -- an fvar-free entry that becomes an `fvar` was a `bvar`
    rcases instSeq_fvar_cases _ _ _ _ _ hfk with ⟨j, hj⟩ | ⟨ty', hj⟩
    case _ =>
      rw [hj] at hfk
      -- it cannot sit above the sequence's top cut
      have hle : j ≤ nP + l - 1 := by
        by_cases hgt : nP + l - 1 < j
        · obtain ⟨j', hj'⟩ := instSeq_bvar_above (fvsP ++ rest) (nP + l - 1) j
            (by omega) hgt
          rw [hj'] at hfk
          exact absurd hfk (by simp)
        · omega
      -- so it hits the opener list, at the index the openers' distinctness forces
      have hhit := Expr.instSeq_bvar (fvsP ++ rest) (nP + l - 1) j hclvs hle (by omega)
      rw [hfk] at hhit
      have hidx : nP + l - 1 - j = k := by
        by_cases hlt : nP + l - 1 - j < nP
        · obtain ⟨ty2, hty2⟩ := hfvsP _ hlt
          rw [List.getElem?_append_left (by omega), hty2] at hhit
          exact (Expr.fvar.inj (Option.some.inj hhit)).1
        · rw [List.getElem?_append_right (by omega)] at hhit
          have hmem : Expr.fvar k ty ∈ rest :=
            List.mem_of_getElem? hhit
          obtain ⟨j2, ty2, heq, hge⟩ := hrest _ hmem
          rw [(Expr.fvar.inj heq).1] at hk
          omega
      rw [hj]
      simp only [structPsAt, List.getElem_map, List.getElem_range]
      rw [show j = l + nP - 1 - k from by omega]
    case _ =>
      exact absurd (hcl _ (List.getElem_mem h1)) (by rw [hj]; simp [Expr.hasFvar])

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

/-- Every reachable `fvar` index bounded is `fvarsBelow` (the leaf
list's spelling of the same fact; `fvarsBelow` does not descend into an
`fvar`'s annotation, so the leaf's own head is all the `fvar` case
needs). -/
theorem fvarsBelow_of_fvarLeaves {k : Nat} :
    ∀ (e : Expr), (∀ l ∈ e.fvarLeaves, l.1 < k) → Expr.fvarsBelow k e := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro h
    exact h (idx, ty) (by rw [Expr.fvarLeaves]; exact List.mem_cons_self)
  | app f a ihf iha =>
    intro h
    rw [Expr.fvarLeaves] at h
    exact ⟨ihf (fun l hl => h l (List.mem_append_left _ hl)),
      iha (fun l hl => h l (List.mem_append_right _ hl))⟩
  | lam ty b m ihty ihb =>
    intro h
    rw [Expr.fvarLeaves] at h
    exact ⟨ihty (fun l hl => h l (List.mem_append_left _ hl)),
      ihb (fun l hl => h l (List.mem_append_right _ hl))⟩
  | forallE ty b m ihty ihb =>
    intro h
    rw [Expr.fvarLeaves] at h
    exact ⟨ihty (fun l hl => h l (List.mem_append_left _ hl)),
      ihb (fun l hl => h l (List.mem_append_right _ hl))⟩
  | letE ty v b ihty ihv ihb =>
    intro h
    rw [Expr.fvarLeaves] at h
    exact ⟨ihty (fun l hl => h l (List.mem_append_left _ (List.mem_append_left _ hl))),
      ihv (fun l hl => h l (List.mem_append_left _ (List.mem_append_right _ hl))),
      ihb (fun l hl => h l (List.mem_append_right _ hl))⟩
  | proj sn i pe ih =>
    intro h
    rw [Expr.fvarLeaves] at h
    exact ih h
  | _ => intro _; trivial

/-- Closing the leading `k` variable levels leaves no free variable
behind. -/
theorem fvarsBelow_abstractRange {k : Nat} :
    ∀ (e : Expr) (c : Nat), Expr.fvarsBelow k e →
      Expr.fvarsBelow 0 (e.abstractRange 0 k c) := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro c h
    show Expr.fvarsBelow 0 (Expr.abstractRange (.fvar idx ty) 0 k c)
    have hlt : idx < k := h
    rw [Expr.abstractRange, if_pos (⟨Nat.zero_le _, by omega⟩)]
    trivial
  | app f a ihf iha => intro c h; exact ⟨ihf c h.1, iha c h.2⟩
  | lam ty b m ihty ihb => intro c h; exact ⟨ihty c h.1, ihb (c + 1) h.2⟩
  | forallE ty b m ihty ihb => intro c h; exact ⟨ihty c h.1, ihb (c + 1) h.2⟩
  | letE ty v b ihty ihv ihb => intro c h; exact ⟨ihty c h.1, ihv c h.2.1, ihb (c + 1) h.2.2⟩
  | proj sn i pe ih => intro c h; exact ih c h
  | _ => intro _ _; trivial

/-- `fvarsBelow` survives a whole instantiation sequence. -/
theorem fvarsBelow_instSeq {d : Nat} :
    ∀ (as : List Expr) (t : Nat) {e : Expr},
      (∀ a ∈ as, Expr.fvarsBelow d a) → Expr.fvarsBelow d e →
      Expr.fvarsBelow d (Expr.instSeq as t e) := by
  intro as
  induction as with
  | nil => intro _ _ _ he; exact he
  | cons a as ih =>
    intro t e ha he
    exact ih (t - 1) (fun b hb => ha b (List.mem_cons_of_mem _ hb))
      (Expr.fvarsBelow_instantiate1_gen (ha a List.mem_cons_self) t he)

/-- **THE ROUND TRIP THE OTHER WAY** (task #315 WIDE (2″)): opening a
body that has NO free variable of its own at a variable list whose
`j`-th entry is an `fvar` with index `j`, and closing the leading `k`
levels again, returns the body ON THE NOSE — annotations included,
because `abstractRange` never reads an `fvar`'s annotation.

`instSeq_abstractRange_fvs_at` (`NestedCopyGlue.lean`) is the same trip
started from the other end, and it needs the openers' annotations
PINNED (`fvarConsistent`) because the body's own leaves carry
annotations of their own.  This direction needs no such hypothesis, and
needs instead that the body carry no `fvar` the abstraction could
capture — which is what `fvarsBelow 0` says.

Its consumer is the one fact `ContainerModeled.pinsDistinct` is short
of: the own-pin TABLE's entries are the recorded pins with every
parameter `fvar`'s annotation replaced by a SYNTHETIC one, so
annotation-erasure stands between "the recorded pins are distinct" and
"the table's entries are distinct" — and erasure is not injective in
general.  This trip is what puts the annotations back. -/
theorem abstractRange_instSeq_fvs :
    ∀ (k : Nat) (fvs : List Expr) (e : Expr) (c : Nat), fvs.length = k →
      (∀ j, j < k → ∃ ty, fvs[j]? = some (Expr.fvar j ty)) →
      (∀ a ∈ fvs, a.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow 0 e → e.looseBVarsBounded (k + c) = true →
      (Expr.instSeq fvs (k + c - 1) e).abstractRange 0 k c = e := by
  intro k
  induction k with
  | zero =>
    intro fvs e c hlen _ _ _ _
    obtain rfl : fvs = [] := List.eq_nil_of_length_eq_zero hlen
    show (e).abstractRange 0 0 c = e
    exact abstractRange_zero e 0 c
  | succ k ih =>
    intro fvs e c hlen hidx hcl hfv hb
    obtain ⟨fvs', x, rfl⟩ : ∃ fvs' x, fvs = fvs' ++ [x] := by
      rcases List.eq_nil_or_concat fvs with rfl | ⟨l', b, rfl⟩
      · simp at hlen
      · exact ⟨l', b, by simp⟩
    have hlen' : fvs'.length = k := by simpa using hlen
    have hlast : (fvs' ++ [x])[k]? = some x := by
      rw [List.getElem?_append_right (by omega), hlen']
      simp
    obtain ⟨tyk, htyk⟩ := hidx k (by omega)
    obtain rfl : x = Expr.fvar k tyk := by
      rw [hlast] at htyk; exact Option.some.inj htyk
    have hidx' : ∀ j, j < k → ∃ ty, fvs'[j]? = some (Expr.fvar j ty) := by
      intro j hj
      obtain ⟨ty, hty⟩ := hidx j (by omega)
      refine ⟨ty, ?_⟩
      rwa [List.getElem?_append_left (by omega)] at hty
    have hcl' : ∀ a ∈ fvs', a.looseBVarsBounded 0 = true :=
      fun a ha => hcl a (List.mem_append_left _ ha)
    have hfvs' : ∀ a ∈ fvs', Expr.fvarsBelow k a := by
      intro a ha
      obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
      have hjlt : j < k := by
        rcases Nat.lt_or_ge j fvs'.length with h | h
        · omega
        · rw [List.getElem?_eq_none h] at hj; exact nomatch hj
      obtain ⟨ty, hty⟩ := hidx' j hjlt
      rw [hj] at hty
      obtain rfl : a = Expr.fvar j ty := Option.some.inj hty
      show j < k
      exact hjlt
    have hbmid : (Expr.instSeq fvs' (k + c) e).looseBVarsBounded (c + 1) = true := by
      have h := looseBVarsBounded_instSeq_gen fvs' (k + c) e hcl'
        (by rw [show k + c + 1 = k + 1 + c from by omega]; exact hb) (by omega)
      rwa [hlen', show k + c + 1 - k = c + 1 from by omega] at h
    have hfvmid : Expr.fvarsBelow k (Expr.instSeq fvs' (k + c) e) :=
      fvarsBelow_instSeq fvs' (k + c) hfvs' (Expr.fvarsBelow_mono (Nat.zero_le k) hfv)
    have hstep : Expr.instSeq (fvs' ++ [Expr.fvar k tyk]) (k + 1 + c - 1) e
        = (Expr.instSeq fvs' (k + c) e).instantiate1 (Expr.fvar k tyk) c := by
      rw [Expr.instSeq_append, hlen', show k + 1 + c - 1 = k + c from by omega,
        show k + c - k = c from by omega]
      rfl
    rw [hstep, abstractRange_succ, Nat.zero_add,
      instantiate1_abstract1_self _ c hfvmid hbmid]
    have hih := ih fvs' e (c + 1) hlen' hidx' hcl' hfv
      (by rw [show k + (c + 1) = k + 1 + c from by omega]; exact hb)
    rwa [show k + (c + 1) - 1 = k + c from by omega] at hih

/-- **THE TWO SPELLINGS OF "THE CONTAINER'S OWN SCOPE" AGREE** (task
#315 WIDE (1′)).

The own-pin reader's cut (`nestedInstMapOkAt`, and K.61's inversion)
instantiates a field's spine with the parameter openers REVERSED, from
the cut `l` the field's earlier binders add; the model's
`PinSyn.ownAt` closes the recorded pin over the parameters and reopens
it with `instSeq` at the descending cuts `nP - 1 … 0`.  Both send the
parameter variable `i` to `containerParamOpeners nP`'s `i`-th entry, so
on a body bounded at `nP` — a pin closed over the parameters, lifted
past the field binders — they compute the same expression.

Three steps: the bulk form at cut `l` IS the `instantiate1` fold at the
descending cuts (`instSpine_eq_instantiateList_at`); the fold drops past
the lift because every opener is closed (`instSeq_liftLooseBVars`); and
what is left is closed — a full argument list closes a body bounded at
its length — so the lift that comes back is the identity. -/
theorem instantiateList_openers_eq_instSeq (nP l : Nat) {A : Expr}
    (hA : A.looseBVarsBounded nP = true) :
    Expr.instantiateList (A.liftLooseBVars l 0) (containerParamOpeners nP).reverse l
      = Expr.instSeq (containerParamOpeners nP) (nP - 1) A := by
  have hlenO : (containerParamOpeners nP).length = nP := by
    simp [containerParamOpeners]
  have hclO : ∀ a ∈ containerParamOpeners nP, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    rfl
  rw [← Expr.instSpine_eq_instantiateList_at, Expr.instSpine_eq_instSeq, hlenO,
    Expr.instSeq_liftLooseBVars (kL := l) (c := 0) _ (l + nP - 1) hclO (by rw [hlenO]; omega),
    show l + nP - 1 - l = nP - 1 from by omega]
  refine Expr.liftLooseBVars_eq_self ?_
  cases nP with
  | zero =>
    rw [show containerParamOpeners 0 = [] from by simp [containerParamOpeners]]
    exact hA
  | succ n =>
    exact looseBVarsBounded_instSeq _ n _ hclO (by simpa using hA) (by rw [hlenO])

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

/-! ## Leaves of an application spine (task #315 L-B) -/

/-- The head's leaves are the spine's. -/
theorem fvarLeaves_mkAppN_head : ∀ (xs : List Expr) {f : Expr} {l : Nat × Expr},
    l ∈ f.fvarLeaves → l ∈ (Expr.mkAppN f xs).fvarLeaves
  | [], _, _, hl => hl
  | x :: xs, f, l, hl => by
    refine fvarLeaves_mkAppN_head xs (f := .app f x) ?_
    simp only [Expr.fvarLeaves, List.mem_append]
    exact Or.inl hl

/-- **An argument's leaves are the spine's** — the converse of
`fvarLeaves_mkAppN`, which is what carries a pin's scope (K.30) to its
components. -/
theorem fvarLeaves_mkAppN_arg : ∀ (xs : List Expr) {f x : Expr} {l : Nat × Expr},
    x ∈ xs → l ∈ x.fvarLeaves → l ∈ (Expr.mkAppN f xs).fvarLeaves
  | y :: xs, f, x, l, hx, hl => by
    rcases List.mem_cons.mp hx with rfl | hx
    · refine fvarLeaves_mkAppN_head xs (f := .app f x) ?_
      simp only [Expr.fvarLeaves, List.mem_append]
      exact Or.inr hl
    · exact fvarLeaves_mkAppN_arg xs hx hl

/-! ## The instantiated body's frame (task #315 L-B, DESIGN §U.33 (c) 4) -/

/-- **The copy's constructor body is closed and scoped by the pin's
components**: `mkCopy` instantiates a STORED constructor's type — no
`fvar` leaf, no loose bvar, and level substitution touches neither
(`hasFvar_instantiateLevelParams`,
`looseBVarsBounded_instantiateLevelParams`) — at the pin's components,
so the result is bounded (`looseBVarsBounded_instPis`) and every leaf
it has is one of the components' (`instPis_instPisAt` +
`instPisAt_fvarLeaves`), hence one of the block's own parameter
openers (K.30).  This is exactly what `instSeq_abstractRange_fvs` asks
of the body it closes and reopens (DESIGN §U.33 (c) step 4). -/
theorem instPisILP_frame {ks : List Name} {us : List Level} {T : Expr}
    {Ds : List Expr} {cI : Expr} {params : List Expr}
    (h : Expr.instPis (Expr.instantiateLevelParams ks us T) Ds = some cI)
    (hb : T.looseBVarsBounded 0 = true) (hf : T.hasFvar = false)
    (hcl : ∀ a ∈ Ds, a.looseBVarsBounded 0 = true)
    (hlv : ∀ a ∈ Ds, ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ params) :
    cI.looseBVarsBounded 0 = true ∧ ∀ l ∈ cI.fvarLeaves, Expr.fvar l.1 l.2 ∈ params := by
  refine ⟨looseBVarsBounded_instPis Ds _ _
    (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb) hcl h, fun l hl => ?_⟩
  obtain ⟨ds, hds⟩ := instPis_instPisAt Ds _ _ h
  rcases instPisAt_fvarLeaves Ds _ hds l hl with hl' | ⟨a, ha, hal⟩
  · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar
      (by rw [Expr.hasFvar_instantiateLevelParams]; exact hf)] at hl'
    exact nomatch hl'
  · exact hlv a ha l hal

/-! ## The openers, replaced by the components (task #315 L-B, DESIGN §U.76)

`mkCopy` instantiates a container constructor's parameter telescope at
a pin's COMPONENTS, while the restore table closes a recorded pin at
the block's parameter OPENERS (`restoreTbl`:
`Expr.abstractRange q.pin 0 p.nP 0`).  Lane M7-3's
`ContainerOwnPinsSyn.toReadOf` reads a recorded pin at ANOTHER
instantiation, and needs the two to be one substitution: **the
identity run, closed at the openers and re-opened at an argument
list, is the run at that list** (DESIGN §U.73 (d) (C), the law lane
M7-3 asked for).

The bridge is a simultaneous `fvar` substitution.  `substFvarList` is
it; `instSeq_abstractRange_substFvarList` says the
`abstractRange`-then-`instSeq` round trip IS that substitution (the
exact-roundtrip lemma `instSeq_abstractRange_fvs` is its special case
at the openers themselves), and `instPis_substFvarList` says it
commutes with a telescope instantiation.  `instPis_openers_subst`
composes the two. -/

/-- **A SIMULTANEOUS `fvar` SUBSTITUTION**: the `j`-th free variable
becomes the `j`-th entry of `as`, and a variable past the list stays
put, annotation and all.  As in `Expr.abstractRange` (and
`Expr.abstract1`) the walk does not descend into a `fvar`'s type
annotation — which is what makes it the composite of the two.

`@[expose]`: lane M7-3's `ContainerOwnPinsSyn.toReadOf` reads a pin off
the instantiated recursor type node by node, so the consumer unfolds
this walk. -/
@[expose] def substFvarList (as : List Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx ty => (as[idx]?).getD (.fvar idx ty)
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f b => .app (substFvarList as f) (substFvarList as b)
  | .lam ty body m => .lam (substFvarList as ty) (substFvarList as body) m
  | .forallE ty body m => .forallE (substFvarList as ty) (substFvarList as body) m
  | .letE ty val body =>
    .letE (substFvarList as ty) (substFvarList as val) (substFvarList as body)
  | .lit l => .lit l
  | .proj s i e => .proj s i (substFvarList as e)

/-- A term with no free variable is untouched. -/
theorem substFvarList_eq_self (as : List Expr) :
    ∀ {e : Expr}, e.hasFvar = false → substFvarList as e = e := by
  intro e
  induction e with
  | fvar idx ty _ => intro h; exact nomatch h
  | _ => intro h <;> simp_all [substFvarList, Expr.hasFvar]

/-- The substitution's own values are closed (a variable past the list
is its own, and a `fvar` has no loose bound variable). -/
private theorem substFvarList_fvar_bounded {as : List Expr}
    (hcl : ∀ a ∈ as, a.looseBVarsBounded 0 = true) (idx : Nat) (ty : Expr) :
    ((as[idx]?).getD (Expr.fvar idx ty)).looseBVarsBounded 0 = true := by
  rcases h : as[idx]? with _ | a
  · rfl
  · simpa using hcl a (List.mem_of_getElem? h)

/-- **THE SUBSTITUTION COMMUTES WITH OPENING A BINDER**: the values
are closed, so the opening does not reach into them. -/
theorem substFvarList_instantiate1 {as : List Expr}
    (hcl : ∀ a ∈ as, a.looseBVarsBounded 0 = true) :
    ∀ (e v : Expr) (t : Nat),
      substFvarList as (e.instantiate1 v t)
        = (substFvarList as e).instantiate1 (substFvarList as v) t := by
  intro e
  induction e with
  | bvar i =>
    intro v t
    by_cases h1 : i = t
    · subst h1; simp [Expr.instantiate1, substFvarList]
    · by_cases h2 : i > t <;>
        simp [Expr.instantiate1, substFvarList, h1, h2]
  | fvar idx ty _ =>
    intro v t
    show substFvarList as (Expr.fvar idx ty) = _
    exact (Expr.instantiate1_eq_self
      (Expr.looseBVarsBounded_mono (Nat.zero_le t)
        (substFvarList_fvar_bounded hcl idx ty))).symm
  | app f b ihf ihb =>
    intro v t
    simp only [Expr.instantiate1, substFvarList, ihf, ihb]
  | lam ty body m ihty ihb =>
    intro v t
    simp only [Expr.instantiate1, substFvarList, ihty, ihb]
  | forallE ty body m ihty ihb =>
    intro v t
    simp only [Expr.instantiate1, substFvarList, ihty, ihb]
  | letE ty val body ihty ihv ihb =>
    intro v t
    simp only [Expr.instantiate1, substFvarList, ihty, ihv, ihb]
  | proj s i x ih =>
    intro v t
    simp only [Expr.instantiate1, substFvarList, ih]
  | _ => intro v t; rfl

/-- **THE SUBSTITUTION COMMUTES WITH A TELESCOPE INSTANTIATION**: the
same `∀`-binders are peeled on both sides, and each argument is
substituted in. -/
theorem instPis_substFvarList {as : List Expr}
    (hcl : ∀ a ∈ as, a.looseBVarsBounded 0 = true) :
    ∀ (args : List Expr) (e r : Expr), Expr.instPis e args = some r →
      Expr.instPis (substFvarList as e) (args.map (substFvarList as))
        = some (substFvarList as r) := by
  intro args
  induction args with
  | nil =>
    intro e r h
    simp only [Expr.instPis, Option.some.injEq] at h
    subst h
    rfl
  | cons a args ih =>
    intro e r h
    match e with
    | .forallE ty body m =>
      show Expr.instPis (Expr.forallE (substFvarList as ty) (substFvarList as body) m)
        ((a :: args).map (substFvarList as)) = _
      show Expr.instPis ((substFvarList as body).instantiate1 (substFvarList as a) 0)
        (args.map (substFvarList as)) = _
      rw [← substFvarList_instantiate1 hcl body a 0]
      exact ih _ r h
    | .bvar _ | .fvar .. | .sort _ | .const .. | .app .. | .lam .. | .letE .. | .lit _
    | .proj .. => exact nomatch h

/-! ### The instantiation sequence, node by node

`Expr.instSeq_forallE` and `Expr.instSeq_app` (`Verify/Subst.lean`)
and `instSeq_bvar_below` above are in the tree; the three remaining
node shapes the round trip below walks through are not, and are proved
here in their spelling. -/

/-- Peel `instSeq` through a `λ`-binder (the `∀` twin of
`Expr.instSeq_forallE`). -/
private theorem instSeq_lam' : ∀ (args : List Expr) (t : Nat) (d b : Expr) (m : BinderMeta),
    args.length ≤ t + 1 →
    Expr.instSeq args t (.lam d b m)
      = .lam (Expr.instSeq args t d) (Expr.instSeq args (t + 1) b) m := by
  intro args
  induction args with
  | nil => intro t d b m _; rfl
  | cons a as ih =>
    intro t d b m hlen
    simp only [List.length_cons] at hlen
    show Expr.instSeq as (t - 1)
      (.lam (d.instantiate1 a t) (b.instantiate1 a (t + 1)) m) = _
    rw [ih (t - 1) (d.instantiate1 a t) (b.instantiate1 a (t + 1)) m (by omega)]
    show Expr.lam (Expr.instSeq as (t - 1) (d.instantiate1 a t))
        (Expr.instSeq as (t - 1 + 1) (b.instantiate1 a (t + 1))) m
      = Expr.lam (Expr.instSeq as (t - 1) (d.instantiate1 a t))
        (Expr.instSeq as (t + 1 - 1) (b.instantiate1 a (t + 1))) m
    cases as with
    | nil => rfl
    | cons a2 as2 => rw [show t - 1 + 1 = t + 1 - 1 from by simp only [List.length_cons] at hlen; omega]

/-- Peel `instSeq` through a `let` (only the body is under a binder). -/
private theorem instSeq_letE' : ∀ (args : List Expr) (t : Nat) (ty v b : Expr),
    args.length ≤ t + 1 →
    Expr.instSeq args t (.letE ty v b)
      = .letE (Expr.instSeq args t ty) (Expr.instSeq args t v) (Expr.instSeq args (t + 1) b) := by
  intro args
  induction args with
  | nil => intro t ty v b _; rfl
  | cons a as ih =>
    intro t ty v b hlen
    simp only [List.length_cons] at hlen
    show Expr.instSeq as (t - 1)
      (.letE (ty.instantiate1 a t) (v.instantiate1 a t) (b.instantiate1 a (t + 1))) = _
    rw [ih (t - 1) (ty.instantiate1 a t) (v.instantiate1 a t) (b.instantiate1 a (t + 1))
      (by omega)]
    show Expr.letE (Expr.instSeq as (t - 1) (ty.instantiate1 a t))
        (Expr.instSeq as (t - 1) (v.instantiate1 a t))
        (Expr.instSeq as (t - 1 + 1) (b.instantiate1 a (t + 1)))
      = Expr.letE (Expr.instSeq as (t - 1) (ty.instantiate1 a t))
        (Expr.instSeq as (t - 1) (v.instantiate1 a t))
        (Expr.instSeq as (t + 1 - 1) (b.instantiate1 a (t + 1)))
    cases as with
    | nil => rfl
    | cons a2 as2 => rw [show t - 1 + 1 = t + 1 - 1 from by simp only [List.length_cons] at hlen; omega]

/-- `instSeq` distributes over a projection. -/
private theorem instSeq_proj' : ∀ (args : List Expr) (t : Nat) (s : Name) (i : Nat) (x : Expr),
    Expr.instSeq args t (.proj s i x) = .proj s i (Expr.instSeq args t x) := by
  intro args
  induction args with
  | nil => intro t s i x; rfl
  | cons a as ih =>
    intro t s i x
    show Expr.instSeq as (t - 1) (.proj s i (x.instantiate1 a t)) = _
    rw [ih]
    rfl

/-- The substitution distributes over an application spine — which is
how a recorded pin's components are reached from the instantiated
major-premise domain (`containerOwnPinsAtGo`: the head and the first
`nP` arguments of `dom`). -/
theorem substFvarList_mkAppN (as : List Expr) :
    ∀ (f : Expr) (args : List Expr),
      substFvarList as (Expr.mkAppN f args)
        = Expr.mkAppN (substFvarList as f) (args.map (substFvarList as))
  | _, [] => rfl
  | f, a :: args => by
    show substFvarList as (Expr.mkAppN (.app f a) args) = _
    rw [substFvarList_mkAppN as (.app f a) args]
    rfl

/-- An empty substitution is the identity (as is an empty
abstraction range: `abstractRange_zero`). -/
private theorem substFvarList_nil : ∀ e : Expr, substFvarList [] e = e := by
  intro e
  induction e with
  | fvar idx ty _ => rfl
  | _ => simp_all [substFvarList]

/-- **THE ROUND TRIP AT ANOTHER ARGUMENT LIST** (task #315 L-B, DESIGN
§U.76): closing the leading `nP` free variables above `c` loose
binders and re-opening them at `as` IS the simultaneous substitution
of `as` for them — `instSeq_abstractRange_fvs` at `as` the openers
themselves is the special case where the substitution is the identity.
The values are closed and the term's loose bound variables stay below
the cursor, so the two ranges of bound variables never meet. -/
theorem instSeq_abstractRange_substFvarList (as : List Expr) (nP : Nat)
    (hlen : as.length = nP) (hcl : ∀ a ∈ as, a.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (c : Nat), e.looseBVarsBounded c = true →
      Expr.instSeq as (nP + c - 1) (e.abstractRange 0 nP c) = substFvarList as e := by
  rcases Nat.eq_zero_or_pos nP with hz | hpos
  · subst hz
    obtain rfl : as = [] := List.eq_nil_of_length_eq_zero hlen
    intro e c _
    show e.abstractRange 0 0 c = substFvarList [] e
    rw [ConLeche.abstractRange_zero, substFvarList_nil]
  intro e
  induction e with
  | bvar i =>
    intro c hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    show Expr.instSeq as (nP + c - 1) (Expr.bvar i) = _
    rw [instSeq_bvar_below as (nP + c - 1) i (by rw [hlen]; omega)]
    rfl
  | fvar idx ty _ =>
    intro c _
    by_cases hr : idx < nP
    · show Expr.instSeq as (nP + c - 1)
        (if 0 ≤ idx ∧ idx < 0 + nP then Expr.bvar (c + (0 + nP - 1 - idx))
          else Expr.fvar idx ty) = _
      rw [if_pos (by omega)]
      have hj : c + (0 + nP - 1 - idx) ≤ nP + c - 1 := by omega
      have hr' : nP + c - 1 - (c + (0 + nP - 1 - idx)) < as.length := by rw [hlen]; omega
      have hb := Expr.instSeq_bvar as (nP + c - 1) (c + (0 + nP - 1 - idx)) hcl hj hr'
      rw [show nP + c - 1 - (c + (0 + nP - 1 - idx)) = idx from by omega] at hb
      show _ = (as[idx]?).getD (Expr.fvar idx ty)
      rw [hb]
      rfl
    · show Expr.instSeq as (nP + c - 1)
        (if 0 ≤ idx ∧ idx < 0 + nP then Expr.bvar (c + (0 + nP - 1 - idx))
          else Expr.fvar idx ty) = _
      rw [if_neg (by omega)]
      rw [Expr.instSeq_eq_self as (nP + c - 1) (by rfl)]
      show _ = (as[idx]?).getD (Expr.fvar idx ty)
      rw [List.getElem?_eq_none (by rw [hlen]; omega)]
      rfl
  | app f b ihf ihb =>
    intro c hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    show Expr.instSeq as (nP + c - 1)
      (Expr.app (f.abstractRange 0 nP c) (b.abstractRange 0 nP c)) = _
    rw [Expr.instSeq_app, ihf c hb.1, ihb c hb.2]
    rfl
  | lam ty body m ihty ihb =>
    intro c hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    show Expr.instSeq as (nP + c - 1)
      (Expr.lam (ty.abstractRange 0 nP c) (body.abstractRange 0 nP (c + 1)) m) = _
    rw [instSeq_lam' as (nP + c - 1) _ _ m (by rw [hlen]; omega),
      show nP + c - 1 + 1 = nP + (c + 1) - 1 from by omega,
      ihty c hb.1, ihb (c + 1) hb.2]
    rfl
  | forallE ty body m ihty ihb =>
    intro c hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    show Expr.instSeq as (nP + c - 1)
      (Expr.forallE (ty.abstractRange 0 nP c) (body.abstractRange 0 nP (c + 1)) m) = _
    rw [Expr.instSeq_forallE as (nP + c - 1) _ _ m (by rw [hlen]; omega),
      show nP + c - 1 + 1 = nP + (c + 1) - 1 from by omega,
      ihty c hb.1, ihb (c + 1) hb.2]
    rfl
  | letE ty val body ihty ihv ihb =>
    intro c hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    show Expr.instSeq as (nP + c - 1)
      (Expr.letE (ty.abstractRange 0 nP c) (val.abstractRange 0 nP c)
        (body.abstractRange 0 nP (c + 1))) = _
    rw [instSeq_letE' as (nP + c - 1) _ _ _ (by rw [hlen]; omega),
      show nP + c - 1 + 1 = nP + (c + 1) - 1 from by omega,
      ihty c hb.1.1, ihv c hb.1.2, ihb (c + 1) hb.2]
    rfl
  | proj s i x ih =>
    intro c hb
    show Expr.instSeq as (nP + c - 1) (Expr.proj s i (x.abstractRange 0 nP c)) = _
    rw [instSeq_proj' as (nP + c - 1) s i _, ih c hb]
    rfl
  | _ =>
    intro c _
    rw [Expr.instSeq_eq_self as (nP + c - 1) (by rfl)]
    rfl

/-- **THE IDENTITY RUN, RE-OPENED AT THE COMPONENTS, IS THE RUN AT THE
COMPONENTS** (task #315 L-B, DESIGN §U.76 — the law lane M7-3's
`ContainerOwnPinsSyn.toReadOf` consumes, DESIGN §U.73 (d) (C)):
instantiating a closed `∀`-telescope at the block's parameter OPENERS
(and a closed pad), closing the openers again and re-opening at `Ds`
is instantiating it at `Ds` (and the same pad) in the first place.

The telescope is closed (`hf`, `hb`: `mkCopy` runs on a STORED
constructor type), the components are closed (`hDcl`, the elimination
rejects a loose bound variable in a component) and so is the pad
(`hpadb`, `hpadf`: the mimic's extra binders are instantiated at
sorts), which is what keeps the abstraction's range to the openers. -/
theorem instPis_openers_subst {T : Expr} {nP : Nat} {params pad Ds : List Expr} {R₀ : Expr}
    (hf : T.hasFvar = false) (hb : T.looseBVarsBounded 0 = true)
    (hplen : params.length = nP)
    (hidx : ∀ j, j < nP → ∃ ty, params[j]? = some (Expr.fvar j ty))
    (hDlen : Ds.length = nP) (hDcl : ∀ a ∈ Ds, a.looseBVarsBounded 0 = true)
    (hpadb : ∀ a ∈ pad, a.looseBVarsBounded 0 = true)
    (hpadf : ∀ a ∈ pad, a.hasFvar = false)
    (h0 : Expr.instPis T (params ++ pad) = some R₀) :
    Expr.instPis T (Ds ++ pad)
      = some (Expr.instSeq Ds (nP - 1) (R₀.abstractRange 0 nP 0)) := by
  -- the arguments, substituted: the openers become the components, the pad stays
  have hmap : (params ++ pad).map (substFvarList Ds) = Ds ++ pad := by
    rw [List.map_append]
    congr 1
    · refine List.ext_getElem (by rw [List.length_map, hplen, hDlen]) ?_
      intro n h1 h2
      rw [List.getElem_map]
      have hn : n < nP := by rw [List.length_map, hplen] at h1; exact h1
      obtain ⟨ty, hty⟩ := hidx n hn
      rw [List.getElem?_eq_getElem (by rw [hplen]; exact hn)] at hty
      rw [(by simpa using hty : params[n] = Expr.fvar n ty)]
      show (Ds[n]?).getD (Expr.fvar n ty) = _
      rw [List.getElem?_eq_getElem (by rw [hDlen]; exact hn)]
      rfl
    · refine List.ext_getElem (by rw [List.length_map]) ?_
      intro n h1 _
      rw [List.getElem_map]
      exact substFvarList_eq_self Ds (hpadf _ (List.getElem_mem _))
  -- the run at the components, by the commutation
  have hrun := instPis_substFvarList hDcl (params ++ pad) T R₀ h0
  rw [substFvarList_eq_self Ds hf, hmap] at hrun
  rw [hrun]
  -- the identity run is closed, so the round trip is the substitution
  have hb0 : R₀.looseBVarsBounded 0 = true := by
    refine looseBVarsBounded_instPis (params ++ pad) T R₀ hb (fun a ha => ?_) h0
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨n, hn⟩ := List.getElem?_of_mem ha
      obtain ⟨ty, hty⟩ := hidx n (by
        have : n < params.length := by
          rcases Nat.lt_or_ge n params.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hn; exact nomatch hn
        omega)
      rw [hty] at hn
      rw [← Option.some.inj hn]
      rfl
    · exact hpadb a ha
  have := instSeq_abstractRange_substFvarList Ds nP hDlen hDcl R₀ 0 hb0
  rw [show nP + 0 - 1 = nP - 1 from by omega] at this
  rw [this]

/-! ### Level instantiation, across the same two walks (task #315 M7-3
session 18)

K.47 records the own-pin table at the block's OWN level arguments —
`p.lps.map Level.param`, the IDENTITY substitution — and a reader asks
for it at some other `lvls`.  So the recorded run has to move across
`Expr.instantiateLevelParams` before `instPis_openers_subst` moves it
across the components, and the closing of the openers has to commute
with it as well. -/

/-- **LEVEL INSTANTIATION COMMUTES WITH A TELESCOPE INSTANTIATION**:
the same `∀`-binders are peeled on both sides, and each argument is
substituted level-instantiated.  The twin of `instPis_substFvarList`
for `Expr.instantiateLevelParams`. -/
theorem instPis_ilp (ks : List Name) (us : List Level) :
    ∀ (args : List Expr) (e r : Expr), Expr.instPis e args = some r →
      Expr.instPis (Expr.instantiateLevelParams ks us e)
          (args.map (Expr.instantiateLevelParams ks us))
        = some (Expr.instantiateLevelParams ks us r) := by
  intro args
  induction args with
  | nil =>
    intro e r h
    simp only [Expr.instPis, Option.some.injEq] at h
    subst h
    rfl
  | cons a args ih =>
    intro e r h
    match e with
    | .forallE ty body m =>
      show Expr.instPis (Expr.forallE (Expr.instantiateLevelParams ks us ty)
          (Expr.instantiateLevelParams ks us body) ⟨Level.substPW ks us m.pw⟩)
        ((a :: args).map (Expr.instantiateLevelParams ks us)) = _
      show Expr.instPis ((Expr.instantiateLevelParams ks us body).instantiate1
        (Expr.instantiateLevelParams ks us a)) (args.map (Expr.instantiateLevelParams ks us)) = _
      rw [← ilp_instantiate1 ks us body 0]
      exact ih _ r h
    | .bvar _ | .fvar .. | .sort _ | .const .. | .app .. | .lam .. | .letE .. | .lit _
    | .proj .. => exact nomatch h

/-! ### A major premise's constant head survives instantiation

A recursor's STORED type is where every route records the shape of its
major premise (`EnvWF`'s recursor clause: `stripPis mI` lands on a `∀`
whose domain is headed by a `.const`), and every READER sees that domain
level-instantiated and substituted at the caller's `mI` arguments.  The
head NAME is the same on both sides: `Expr.instantiateLevelParams`
rewrites a `.const`'s level arguments and nothing else, and the
substitutions `Expr.instPis` performs can only replace a head that is a
loose `bvar`.  `instPis_ilp_major_head` is that statement, once, for
every consumer that has the stored shape and wants the instantiated
one; the two telescope readings it composes are the
`.forallE`-with-constant-head twins of the `sort` kit in
`NestedCopySort.lean`. -/

/-- **INSTANTIATING A BINDER KEEPS A CONSTANT-HEADED RESIDUAL `∀`**:
`Expr.instantiate1` substitutes into the residual at its depth
(`Expr.stripPis_instantiate1_isSome`/`_eq`), and a constant head is not
a `bvar`, so it stays (`Expr.getAppFn_instantiate1_const`). -/
theorem Expr.stripPis_instantiate1_constHead {v : Expr} {D : Name} (k j : Nat) {e : Expr}
    {bs : List (Expr × BinderMeta)} {dom body : Expr} {bm : BinderMeta} {us : List Level}
    (h : e.stripPis k = some (bs, .forallE dom body bm))
    (hd : dom.getAppFn = .const D us) :
    ∃ (bs' : List (Expr × BinderMeta)) (dom' body' : Expr) (bm' : BinderMeta),
      (e.instantiate1 v j).stripPis k = some (bs', .forallE dom' body' bm') ∧
        dom'.getAppFn = .const D us := by
  have hsome : ((e.instantiate1 v j).stripPis k).isSome :=
    Expr.stripPis_instantiate1_isSome k j (by rw [h]; rfl)
  cases hq : (e.instantiate1 v j).stripPis k with
  | none => rw [hq] at hsome; exact nomatch hsome
  | some q =>
    obtain ⟨qbs, qbody⟩ := q
    obtain ⟨hbody, -⟩ := Expr.stripPis_instantiate1_eq k j h hq
    exact ⟨qbs, dom.instantiate1 v (j + k), body.instantiate1 v (j + k + 1), bm,
      by rw [hbody]; rfl, Expr.getAppFn_instantiate1_const hd⟩

/-- **LEVEL INSTANTIATION KEEPS A CONSTANT-HEADED RESIDUAL `∀`**: the
same binders are peeled on both sides
(`Expr.stripPis_instantiateLevelParams_isSome`/`_eq`) and
`Expr.instantiateLevelParams` rewrites a `.const`'s level arguments
without touching its NAME (`Expr.getAppFn_instantiateLevelParams`). -/
theorem Expr.stripPis_instantiateLevelParams_constHead {ks : List Name} {vs : List Level}
    {D : Name} (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {dom body : Expr}
    {bm : BinderMeta} {us : List Level}
    (h : e.stripPis k = some (bs, .forallE dom body bm))
    (hd : dom.getAppFn = .const D us) :
    ∃ (bs' : List (Expr × BinderMeta)) (dom' body' : Expr) (bm' : BinderMeta)
      (us' : List Level),
      (e.instantiateLevelParams ks vs).stripPis k = some (bs', .forallE dom' body' bm') ∧
        dom'.getAppFn = .const D us' := by
  have hsome : ((e.instantiateLevelParams ks vs).stripPis k).isSome :=
    Expr.stripPis_instantiateLevelParams_isSome ks vs k (by rw [h]; rfl)
  cases hq : (e.instantiateLevelParams ks vs).stripPis k with
  | none => rw [hq] at hsome; exact nomatch hsome
  | some q =>
    obtain ⟨qbs, qbody⟩ := q
    obtain ⟨hbody, -⟩ := Expr.stripPis_instantiateLevelParams_eq ks vs k h hq
    refine ⟨qbs, dom.instantiateLevelParams ks vs, body.instantiateLevelParams ks vs,
      ⟨Level.substPW ks vs bm.pw⟩, us.map (Level.subst ks vs), by rw [hbody]; rfl, ?_⟩
    rw [Expr.getAppFn_instantiateLevelParams, hd]
    rfl

/-- **A TELESCOPE INSTANTIATION READS BACK THE STRIPPED RESIDUAL'S
HEAD**: when the arguments eat exactly the stripped binders, what
`Expr.instPis` returns is that residual `∀` — substituted, hence with
the same constant head.  (`Expr.instPis_stripPis_sort`'s twin at a
constant-headed domain; the residual arity is `0` because `args.length`
is the strip count itself.) -/
theorem Expr.instPis_stripPis_constHead {D : Name} :
    ∀ (as : List Expr) {e : Expr} {bs : List (Expr × BinderMeta)}
      {dom body : Expr} {bm : BinderMeta} {us : List Level} {r : Expr},
      e.stripPis as.length = some (bs, .forallE dom body bm) →
      dom.getAppFn = .const D us →
      e.instPis as = some r →
      ∃ (dom' body' : Expr) (bm' : BinderMeta) (us' : List Level),
        r = .forallE dom' body' bm' ∧ dom'.getAppFn = .const D us' := by
  intro as
  induction as with
  | nil =>
    intro e bs dom body bm us r h hd hr
    simp only [List.length_nil, Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    simp only [Expr.instPis, Option.some.injEq] at hr
    exact ⟨dom, body, bm, us, by rw [← hr, ← h.2], hd⟩
  | cons a as ih =>
    intro e bs dom body bm us r h hd hr
    rw [show (a :: as).length = as.length + 1 from rfl] at h
    match e, h, hr with
    | .forallE d b m, h, hr =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis as.length with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        obtain ⟨pbs, pbody⟩ := p
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨bs', dom', body', bm', hbs', hd'⟩ :=
          Expr.stripPis_instantiate1_constHead (v := a) as.length 0 hs hd
        exact ih hbs' hd' (by simpa only [Expr.instPis] using hr)
    | .bvar _, h, _ | .fvar _ _, h, _ | .sort _, h, _ | .const _ _, h, _ | .app _ _, h, _
    | .lam _ _ _, h, _ | .letE _ _ _, h, _ | .lit _, h, _ | .proj _ _ _, h, _ =>
      simp [Expr.stripPis] at h

/-- **THE MAJOR PREMISE'S HEAD NAME IS THE STORED ONE** (task #315
M7-3 session 18): a type whose `mI`-binder strip lands on a `∀` with a
`.const D`-headed domain still has a `.const D`-headed one after level
instantiation and after `Expr.instPis` at `mI` arguments.  Only the
level arguments move.

This is the ONE step between a recursor's stored major-premise shape
(what `EnvWF` records, since every route stores what it generates) and
the domain a reader of the INSTANTIATED type sees — `Model`'s
`recMajorHeadStored_of_stripPis` is its consumer, and any producer of
the stored shape can cite it here rather than re-derive it. -/
theorem instPis_ilp_major_head {D : Name} {T : Expr} {mI : Nat} {args : List Expr}
    {ks : List Name} {vs : List Level} {pre : List (Expr × BinderMeta)}
    {dom₀ body₀ dom body : Expr} {bm₀ bm : BinderMeta} {us₀ : List Level}
    (hstrip : T.stripPis mI = some (pre, .forallE dom₀ body₀ bm₀))
    (hhead : dom₀.getAppFn = .const D us₀)
    (hlen : args.length = mI)
    (hinst : Expr.instPis (T.instantiateLevelParams ks vs) args
      = some (.forallE dom body bm)) :
    ∃ us', dom.getAppFn = .const D us' := by
  obtain ⟨pre₁, dom₁, body₁, bm₁, us₁, hstrip₁, hhead₁⟩ :=
    Expr.stripPis_instantiateLevelParams_constHead (ks := ks) (vs := vs) mI hstrip hhead
  obtain ⟨dom₂, body₂, bm₂, us₂, hr, hhead₂⟩ :=
    Expr.instPis_stripPis_constHead args (by rw [hlen]; exact hstrip₁) hhead₁ hinst
  injection hr with hdom _ _
  exact ⟨us₂, by rw [hdom]; exact hhead₂⟩

/-- **CLOSING A RANGE OF FREE VARIABLES COMMUTES WITH LEVEL
INSTANTIATION**: neither walk touches the other's data.  A variable in
the range becomes a bound variable, which carries no level argument at
all, and a variable outside it keeps its annotation — which is the only
place `instantiateLevelParams` acts on a `fvar`, and the one
`Expr.abstractRange` does not descend into. -/
theorem abstractRange_ilp (ks : List Name) (us : List Level) (d k : Nat) :
    ∀ (e : Expr) (c : Nat),
      (Expr.instantiateLevelParams ks us e).abstractRange d k c
        = Expr.instantiateLevelParams ks us (e.abstractRange d k c) := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro c
    show (if d ≤ idx ∧ idx < d + k then Expr.bvar (c + (d + k - 1 - idx))
        else Expr.fvar idx (Expr.instantiateLevelParams ks us ty))
      = Expr.instantiateLevelParams ks us
        (if d ≤ idx ∧ idx < d + k then Expr.bvar (c + (d + k - 1 - idx))
          else Expr.fvar idx ty)
    by_cases h : d ≤ idx ∧ idx < d + k
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]
      rfl
  | _ => intro c <;> simp_all [Expr.abstractRange, Expr.instantiateLevelParams]

end ConLeche
