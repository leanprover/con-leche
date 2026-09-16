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

end ConLeche
