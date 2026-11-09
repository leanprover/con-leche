module

public import ConLeche.Verify.BetaSpine
import ConLeche.Verify.Abstract
import ConLeche.Verify.AbstractRange
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Leaves

public section

/-!
# Binder-telescope loops and their identification with the chained
bodies (task #72)

The cached checker's binder cases (`inferLamsI`/`inferPisI`,
`ConLeche/Cached/CoreC.lean`) peel a whole binder telescope in one loop
— bulk-opening with an fvar accumulator, substituting only each
binder's domain on the way in, and rebuilding with one `abstractRange`
per domain and one over the leaf.  This file provides the pure mirrors
(generic over the core record, like `BetaSpine`'s) and proves the
**soundness of each loop against the chained spec**: a successful
mirror run at the pure fueled knot is reproduced by the original
one-binder-at-a-time body at some fuel (`inferLams_sound`,
`inferPis_sound`).  The cached walks
(`ConLeche/Verify/Cached/BinderLoopC.lean`) compose their simulation
against the mirrors with these theorems, so the `Expr`-level
specification — and everything above it — is unchanged.

Every *rebuild* phase is a pure fold (no knot calls): the λ-rule
infers only the body, and the ∀-rule infers the codomain sort once at
the leaf.  The only reproduction obligations are the peel phase's
domain checks, the leaf runs, and — for the ∀-loop — the chained rule's
per-level `ensureSort` on an already-built sort (`whnf_sort`).  The
rebuild/chain identification is the pure `abstractRange`/`abstract1`
algebra (`abstractRange_succ`).
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace ConLeche

variable {mode : CheckMode} {eager : Bool}

open Expr

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## The pure mirrors -/

/-- Pure mirror of `inferLamsOutI` (a pure rebuild fold). -/
@[expose] def inferLamsOut (d : Nat) :
    List Expr → Nat → Expr → m Expr
  | [], _j, cur => pure cur
  | tyo :: rest, j, cur =>
    inferLamsOut d rest (j - 1) (Expr.forallE (tyo.abstractRange d j) cur)

/-- Pure mirror of `inferLamsLeafI`: the bulk-opened residual's type,
then the rebuild. -/
@[expose] def inferLamsLeaf (r : CoreFns m) (d : Nat)
    (t : Expr) (k : Nat) (fvs : List Expr)
    (stk : List Expr) : m Expr := do
  let bt ← r.infer (d + k) (t.instantiateList fvs)
  inferLamsOut d stk (k - 1) (bt.abstractRange d k)

/-- Pure mirror of `inferLamsI`. -/
@[expose] def inferLams (r : CoreFns m) (d : Nat) :
    Nat → Expr → Nat → List Expr → List Expr → m Expr
  | fuel + 1, t, k, fvs, stk =>
    match t with
    | .lam ty body => do
      let tyo := ty.instantiateList fvs
      let tty ← r.infer (d + k) tyo
      match ← r.whnf (d + k) tty with
      | .sort _ =>
        inferLams r d fuel body (k + 1)
          (Expr.fvar (d + k) tyo :: fvs) (tyo :: stk)
      | _ => throw (.invalid "expected a sort")
    | t => inferLamsLeaf r d t k fvs stk
  | 0, t, k, fvs, stk => inferLamsLeaf r d t k fvs stk

/-- Pure mirror of `inferPisOutI` (the `imax` fold, pure). -/
@[expose] def inferPisOut : List Level → Level → m Level
  | [], v => pure v
  | u :: rest, v => inferPisOut rest (.imax u v)

/-- Pure mirror of `inferPisLeafI`. -/
@[expose] def inferPisLeaf (r : CoreFns m) (d : Nat)
    (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List Level) : m Expr := do
  let bt ← r.infer (d + k) (t.instantiateList fvs)
  match ← r.whnf (d + k) bt with
  | .sort v => do
    let iv ← inferPisOut stk v
    pure (Expr.sort iv)
  | _ => throw (.invalid "expected a sort")

/-- Pure mirror of `inferPisI`. -/
@[expose] def inferPis (r : CoreFns m) (d : Nat) :
    Nat → Expr → Nat → List Expr → List Level → m Expr
  | fuel + 1, t, k, fvs, stk =>
    match t with
    | .forallE ty body => do
      let tyo := ty.instantiateList fvs
      let tty ← r.infer (d + k) tyo
      match ← r.whnf (d + k) tty with
      | .sort u =>
        inferPis r d fuel body (k + 1)
          (Expr.fvar (d + k) tyo :: fvs) (u :: stk)
      | _ => throw (.invalid "expected a sort")
    | t => inferPisLeaf r d t k fvs stk
  | 0, t, k, fvs, stk => inferPisLeaf r d t k fvs stk

/-! ## The chained tails (wraps) -/

/-- The chained `inferBody` λ-tail folded over the peeled binders
(innermost first, `j` the head entry's binder level): the fold is
pure. -/
@[expose] def inferLamsWrap (d : Nat) :
    List Expr → Nat → Expr → m Expr
  | [], _j, bt => pure bt
  | tyo :: rest, j, bt =>
    inferLamsWrap d rest (j - 1) (.forallE tyo (bt.abstract1 (d + j)))

/-- The chained `inferBody` ∀-tail folded over the peeled binders: per
level, the chained rule's `ensureSort` of the freshly built inner sort
(reproduced by `whnf_sort`), then the `imax`. -/
@[expose] def inferPisWrap (r : CoreFns m) (env : Env)
    (d : Nat) :
    List Level → Nat → Expr → m Expr
  | [], _j, bt => pure bt
  | u :: rest, j, bt => do
    let v ← ensureSort r env (d + j + 1) bt
    inferPisWrap r env d rest (j - 1) (.sort (.imax u v))

/-! ## Unfolding equations -/

section Unfold

variable {r : CoreFns m} {env : Env} {d : Nat}

theorem inferLams_zero (t : Expr) (k : Nat) (fvs : List Expr)
    (stk : List Expr) :
    inferLams r d 0 t k fvs stk
      = inferLamsLeaf r d t k fvs stk := by rfl

theorem inferLams_succ_lam (fuel : Nat) (ty body : Expr)
    (k : Nat) (fvs : List Expr)
    (stk : List Expr) :
    inferLams r d (fuel + 1) (.lam ty body) k fvs stk
      = (do
        let tty ← r.infer (d + k) (ty.instantiateList fvs)
        match ← r.whnf (d + k) tty with
        | .sort _ =>
          inferLams r d fuel body (k + 1)
            (Expr.fvar (d + k) (ty.instantiateList fvs) :: fvs)
            (ty.instantiateList fvs :: stk)
        | _ => throw (.invalid "expected a sort")) := by rfl

theorem inferLams_succ_ne_lam (fuel : Nat) {t : Expr}
    (ht : ∀ ty body, t ≠ .lam ty body) (k : Nat)
    (fvs : List Expr) (stk : List Expr) :
    inferLams r d (fuel + 1) t k fvs stk
      = inferLamsLeaf r d t k fvs stk := by
  cases t with
  | lam ty body => exact absurd rfl (ht ty body)
  | _ => rw [inferLams] <;> exact fun _ _ h => nomatch h

theorem inferPis_zero (t : Expr) (k : Nat) (fvs : List Expr)
    (stk : List Level) :
    inferPis r d 0 t k fvs stk
      = inferPisLeaf r d t k fvs stk := by rfl

theorem inferPis_succ_pi (fuel : Nat) (ty body : Expr)
    (k : Nat) (fvs : List Expr)
    (stk : List Level) :
    inferPis r d (fuel + 1) (.forallE ty body) k fvs stk
      = (do
        let tty ← r.infer (d + k) (ty.instantiateList fvs)
        match ← r.whnf (d + k) tty with
        | .sort u =>
          inferPis r d fuel body (k + 1)
            (Expr.fvar (d + k) (ty.instantiateList fvs) :: fvs)
            (u :: stk)
        | _ => throw (.invalid "expected a sort")) := by rfl

theorem inferPis_succ_ne_pi (fuel : Nat) {t : Expr}
    (ht : ∀ ty body, t ≠ .forallE ty body) (k : Nat)
    (fvs : List Expr) (stk : List Level) :
    inferPis r d (fuel + 1) t k fvs stk
      = inferPisLeaf r d t k fvs stk := by
  cases t with
  | forallE ty body => exact absurd rfl (ht ty body)
  | _ => rw [inferPis] <;> exact fun _ _ h => nomatch h

/-! Shape equations of the fueled bodies on binder nodes (definitional;
the fuel steps once). -/

theorem inferTypeCore_forallE_eq (env : Env) (F d : Nat)
    (ty body : Expr) :
    inferTypeCore mode eager env (F + 1) d (.forallE ty body)
      = (inferTypeCore mode eager env F d ty >>= fun tty =>
         whnf mode eager env F d tty >>= fun w =>
         match w with
         | .sort u =>
           inferTypeCore mode eager env F (d + 1)
               (body.instantiate1 (.fvar d ty)) >>= fun bt =>
             ensureSortCore mode eager env F (d + 1) bt >>= fun v =>
               pure (Expr.sort (.imax u v))
         | _ => throw (.invalid "expected a sort")) := rfl

theorem inferTypeCore_lam_eq (env : Env) (F d : Nat)
    (ty body : Expr) :
    inferTypeCore mode eager env (F + 1) d (.lam ty body)
      = (inferTypeCore mode eager env F d ty >>= fun tty =>
         whnf mode eager env F d tty >>= fun w =>
         match w with
         | .sort _ =>
           inferTypeCore mode eager env F (d + 1)
               (body.instantiate1 (.fvar d ty)) >>= fun bt =>
             pure (Expr.forallE ty (bt.abstract1 d))
         | _ => throw (.invalid "expected a sort")) := rfl

theorem ensureSortCore_eq (env : Env) (F d : Nat) (e : Expr) :
    ensureSortCore mode eager env F d e
      = (whnf mode eager env F d e >>= fun w =>
         match w with
         | .sort u => pure u
         | _ => throw (.invalid "expected a sort")) := rfl

theorem bind_okB {α β : Type} {x : Except CheckError α}
    {g : α → Except CheckError β} {res : β}
    (h : (x >>= g) = .ok res) : ∃ a, x = .ok a ∧ g a = .ok res := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

theorem okB_bind {α β : Type} (a : α)
    {g : α → Except CheckError β} :
    ((Except.ok a : Except CheckError α) >>= g) = g a := rfl

/-- `whnf` is the identity on sorts (two fuel steps in). -/
theorem whnf_sort (env : Env) (F d : Nat) (u : Level) :
    whnf mode eager env (F + 2) d (.sort u) = .ok (.sort u) := by
  -- one iteration of the reduction loop suffices (task #106: the step
  -- budget is `irreducible`, so peel it with its positivity witness)
  obtain ⟨k, hk⟩ := whnfLoopFuel_succ
  rw [whnf_succ]
  show whnfLoop (pureFns mode eager env (F + 1)) env d whnfLoopFuel _ = _
  rw [hk]
  rfl

end Unfold

/-! ## Fixed-fuel (`atF`) spellings -/

section AtF

variable {env : Env}

theorem inferLamsOut_atF (d : Nat) :
    ∀ (stk : List Expr) (j : Nat) (cur : Expr) (F : Nat),
      (inferLamsOut (m := FueledM) d stk j cur).val F
        = inferLamsOut (m := CheckM) d stk j cur
  | [], _, _, _ => rfl
  | _tyo :: rest, j, _cur, F => inferLamsOut_atF d rest (j - 1) _ F

theorem inferLamsLeaf_atF (d : Nat) (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List Expr) (F : Nat) :
    (inferLamsLeaf (fueledFns mode eager env) d t k fvs stk).val F
      = inferLamsLeaf (pureFns mode eager env F) d t k fvs stk := by
  unfold inferLamsLeaf
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  exact inferLamsOut_atF d stk (k - 1) _ F

theorem inferLams_atF (d : Nat) :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List Expr) (F : Nat),
      (inferLams (fueledFns mode eager env) d fuel t k fvs stk).val F
        = inferLams (pureFns mode eager env F) d fuel t k fvs stk
  | 0, t, k, fvs, stk, F => inferLamsLeaf_atF d t k fvs stk F
  | fuel + 1, t, k, fvs, stk, F => by
    by_cases hlam : ∃ ty body, t = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [inferLams_succ_lam, inferLams_succ_lam]
      rw [FueledM.atF_bind]
      congr 1
      funext tty
      rw [FueledM.atF_bind]
      congr 1
      funext w
      cases w <;> first
        | rfl
        | exact inferLams_atF d fuel body (k + 1) _ _ F
    · have ht : ∀ ty body, t ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [inferLams_succ_ne_lam _ ht, inferLams_succ_ne_lam _ ht]
      exact inferLamsLeaf_atF d t k fvs stk F

theorem inferPisOut_atF :
    ∀ (stk : List Level) (v : Level) (F : Nat),
      (inferPisOut (m := FueledM) stk v).val F
        = inferPisOut (m := CheckM) stk v
  | [], _, _ => rfl
  | u :: rest, v, F => inferPisOut_atF rest (.imax u v) F

theorem inferPisLeaf_atF (d : Nat) (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List Level) (F : Nat) :
    (inferPisLeaf (fueledFns mode eager env) d t k fvs stk).val F
      = inferPisLeaf (pureFns mode eager env F) d t k fvs stk := by
  unfold inferPisLeaf
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  rw [FueledM.atF_bind]
  congr 1
  funext w
  cases w <;> try rfl
  case sort v =>
    dsimp only
    rw [FueledM.atF_bind]
    congr 1
    exact inferPisOut_atF stk v F

theorem inferPis_atF (d : Nat) :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List Level) (F : Nat),
      (inferPis (fueledFns mode eager env) d fuel t k fvs stk).val F
        = inferPis (pureFns mode eager env F) d fuel t k fvs stk
  | 0, t, k, fvs, stk, F => inferPisLeaf_atF d t k fvs stk F
  | fuel + 1, t, k, fvs, stk, F => by
    by_cases hpi : ∃ ty body, t = Expr.forallE ty body
    · obtain ⟨ty, body, rfl⟩ := hpi
      rw [inferPis_succ_pi, inferPis_succ_pi]
      rw [FueledM.atF_bind]
      congr 1
      funext tty
      rw [FueledM.atF_bind]
      congr 1
      funext w
      cases w <;> first
        | rfl
        | exact inferPis_atF d fuel body (k + 1) _ _ F
    · have ht : ∀ ty body, t ≠ Expr.forallE ty body :=
        fun ty b hh => hpi ⟨ty, b, hh⟩
      rw [inferPis_succ_ne_pi _ ht, inferPis_succ_ne_pi _ ht]
      exact inferPisLeaf_atF d t k fvs stk F

end AtF

/-! ## Rebuild/wrap identification (pure) and peel soundness -/

section InferSound

variable {env : Env}

/-- The rebuild fold equals the chained `abstract1` fold — pure
`abstractRange` algebra (`abstractRange_succ`), stated at the rebuild
cursor the leaf phase enters with (`stk.length = j + 1`). -/
theorem inferLamsOut_wrap {d : Nat} :
    ∀ (stk : List Expr) (j : Nat) (bt : Expr),
      stk.length = j + 1 →
      inferLamsOut (m := CheckM) d stk j (bt.abstractRange d (j + 1))
        = inferLamsWrap (m := CheckM) d stk j bt := by
  intro stk
  induction stk with
  | nil => intro j bt hlen; exact nomatch hlen
  | cons tyo rest ih =>
    intro j bt hlen
    show inferLamsOut (m := CheckM) d rest (j - 1)
        (Expr.forallE (tyo.abstractRange d j)
          (bt.abstractRange d (j + 1)))
      = inferLamsWrap (m := CheckM) d rest (j - 1)
          (Expr.forallE tyo (bt.abstract1 (d + j)))
    cases rest with
    | nil =>
      obtain rfl : j = 0 := by simpa using hlen
      show Except.ok _ = Except.ok _
      congr 2
      · exact abstractRange_zero ..
      · rw [abstractRange_succ, abstractRange_zero]
    | cons e' rest' =>
      have hnode : Expr.forallE (tyo.abstractRange d j)
          (bt.abstractRange d (j + 1))
          = (Expr.forallE tyo (bt.abstract1 (d + j))).abstractRange
              d ((j - 1) + 1) := by
        have hj : (j - 1) + 1 = j := by
          simp only [List.length_cons] at hlen
          omega
        rw [hj]
        show _ = Expr.forallE (tyo.abstractRange d j 0)
          ((bt.abstract1 (d + j) 0).abstractRange d j 1)
        rw [abstractRange_succ]
      rw [hnode]
      exact ih (j - 1) _ (by
        simp only [List.length_cons] at hlen ⊢
        omega)

/-- Leaf-phase soundness: the mirror's leaf run is the chained
inference of the bulk-opened residual and the (pure) tails. -/
theorem inferLamsLeaf_sound {d : Nat} {t : Expr}
    {k : Nat} {fvs : List Expr} {stk : List Expr} {F : Nat}
    {res : Expr}
    (hlen : stk.length = k)
    (hrun : inferLamsLeaf (pureFns mode eager env F) d t k fvs stk = .ok res) :
    ∃ F', (inferTypeCore mode eager env F' (d + k) (t.instantiateList fvs) >>=
      fun bt => inferLamsWrap (m := CheckM) d stk (k - 1) bt) = .ok res := by
  unfold inferLamsLeaf at hrun
  obtain ⟨bt, hbt, hrun⟩ := bind_okB hrun
  rw [infer_def] at hbt
  refine ⟨F, ?_⟩
  rw [hbt, okB_bind]
  cases stk with
  | nil =>
    obtain rfl : k = 0 := by simpa using hlen.symm
    unfold inferLamsOut at hrun
    rw [abstractRange_zero] at hrun
    exact hrun
  | cons e rest =>
    have hk1 : 1 ≤ k := by rw [← hlen]; simp
    have hkeq : (k - 1) + 1 = k := by omega
    rw [← inferLamsOut_wrap (e :: rest) (k - 1) bt
      (by simp only [List.length_cons] at hlen ⊢; omega), hkeq]
    exact hrun

/-- A successful peel run is reproduced by the chained inference of the
bulk-opened residual followed by the chained tails, at some fuel. -/
theorem inferLams_sound {d : Nat} :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List Expr) (F : Nat) (res : Expr),
      stk.length = k →
      inferLams (pureFns mode eager env F) d fuel t k fvs stk = .ok res →
      ∃ F', (inferTypeCore mode eager env F' (d + k) (t.instantiateList fvs) >>=
        fun bt => inferLamsWrap (m := CheckM) d stk (k - 1) bt) = .ok res := by
  intro fuel
  induction fuel with
  | zero =>
    intro t k fvs stk F res hlen hrun
    rw [inferLams_zero] at hrun
    exact inferLamsLeaf_sound hlen hrun
  | succ fuel ihf =>
    intro t k fvs stk F res hlen hrun
    by_cases hlam : ∃ ty body, t = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [inferLams_succ_lam] at hrun
      obtain ⟨tty, htty, hrun⟩ := bind_okB hrun
      rw [infer_def] at htty
      obtain ⟨w, hww, hrun⟩ := bind_okB hrun
      rw [whnf_def] at hww
      obtain ⟨u, rfl⟩ : ∃ u, w = Expr.sort u := by
        cases w with
        | sort u' => exact ⟨u', rfl⟩
        | bvar i => exact nomatch hrun
        | fvar idx tt => exact nomatch hrun
        | const nm us => exact nomatch hrun
        | app f a => exact nomatch hrun
        | lam tt b => exact nomatch hrun
        | forallE tt b => exact nomatch hrun
        | letE tt vv b => exact nomatch hrun
        | lit l => exact nomatch hrun
        | proj sp i e => exact nomatch hrun
      dsimp only at hrun
      obtain ⟨F', hchain⟩ := ihf body (k + 1) _ _ F res
        (by simpa using hlen) hrun
      obtain ⟨bt, hbt, htail⟩ := bind_okB hchain
      have hlamL : (Expr.lam ty body).instantiateList fvs
          = Expr.lam (ty.instantiateList fvs)
            (body.instantiateList fvs 1) := by
        simp [Expr.instantiateList]
      refine ⟨(max F F') + 1, ?_⟩
      rw [hlamL, inferTypeCore_lam_eq]
      rw [inferTypeCore_mono (Nat.le_max_left F F') htty, okB_bind]
      rw [whnf_mono (Nat.le_max_left F F') hww, okB_bind]
      dsimp only
      rw [show (body.instantiateList fvs 1).instantiate1
          (.fvar (d + k) (ty.instantiateList fvs))
          = body.instantiateList
            (Expr.fvar (d + k) (ty.instantiateList fvs) :: fvs) from
        (Expr.instantiateList_cons ..).symm]
      rw [show d + k + 1 = d + (k + 1) from by omega]
      rw [inferTypeCore_mono (Nat.le_max_right F F') hbt, okB_bind]
      rw [pure_bind]
      rw [show (k + 1 : Nat) - 1 = k from rfl] at htail
      exact htail
    · have ht : ∀ ty body, t ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [inferLams_succ_ne_lam _ ht] at hrun
      exact inferLamsLeaf_sound hlen hrun

/-- The ∀-wrap is fuel monotone (its only runs are `ensureSort`s). -/
theorem inferPisWrap_mono {d : Nat} :
    ∀ {stk : List Level} {j : Nat} {bt : Expr} {F F' : Nat},
      F ≤ F' → ∀ {res : Expr},
      inferPisWrap (pureFns mode eager env F) env d stk j bt = .ok res →
      inferPisWrap (pureFns mode eager env F') env d stk j bt = .ok res := by
  intro stk
  induction stk with
  | nil => intro j bt F F' hle res h; exact h
  | cons u rest ih =>
    intro j bt F F' hle res h
    unfold inferPisWrap at h ⊢
    obtain ⟨v, hv, h⟩ := bind_okB h
    rw [ensureSort_def] at hv
    rw [ensureSort_def, ensureSortCore_mono hle hv, okB_bind]
    exact ih hle h

/-- The `imax`-fold wrap on an explicit sort is the fold mirror's own
run (the chained per-level `ensureSort`s reduce by `whnf_sort`). -/
theorem inferPisWrap_sort {d : Nat} :
    ∀ (stk : List Level) (j : Nat) (v : Level) {F : Nat},
      2 ≤ F →
      inferPisWrap (pureFns mode eager env F) env d stk j (.sort v)
        = (inferPisOut (m := CheckM) stk v).map Expr.sort := by
  intro stk
  induction stk with
  | nil => intro j v F hF; rfl
  | cons u rest ih =>
    intro j v F hF
    show (ensureSort (pureFns mode eager env F) env (d + j + 1) (.sort v) >>=
      fun v' => inferPisWrap (pureFns mode eager env F) env d rest (j - 1)
          (.sort (.imax u v'))) = _
    rw [ensureSort_def, ensureSortCore_eq]
    have hw : whnf mode eager env F (d + j + 1) (.sort v) = .ok (.sort v) := by
      obtain ⟨F₂, rfl⟩ : ∃ F₂, F = F₂ + 2 := ⟨F - 2, by omega⟩
      exact whnf_sort env F₂ (d + j + 1) v
    rw [hw, okB_bind]
    dsimp only
    rw [pure_bind]
    exact ih (j - 1) (.imax u v) hF

/-- Leaf-phase soundness for the ∀-loop. -/
theorem inferPisLeaf_sound {d : Nat} {t : Expr}
    {k : Nat} {fvs : List Expr} {stk : List Level} {F : Nat}
    {res : Expr}
    (hlen : stk.length = k) (hk : 1 ≤ k)
    (hrun : inferPisLeaf (pureFns mode eager env F) d t k fvs stk
      = .ok res) :
    ∃ F', (inferTypeCore mode eager env F' (d + k) (t.instantiateList fvs) >>=
      fun bt => inferPisWrap (pureFns mode eager env F') env d stk
        (k - 1) bt) = .ok res := by
  unfold inferPisLeaf at hrun
  obtain ⟨bt, hbt, hrun⟩ := bind_okB hrun
  rw [infer_def] at hbt
  obtain ⟨w, hww, hrun⟩ := bind_okB hrun
  rw [whnf_def] at hww
  obtain ⟨v, rfl⟩ : ∃ v, w = Expr.sort v := by
    cases w with
    | sort v' => exact ⟨v', rfl⟩
    | bvar i => exact nomatch hrun
    | fvar idx tt => exact nomatch hrun
    | const nm us => exact nomatch hrun
    | app f a => exact nomatch hrun
    | lam tt b => exact nomatch hrun
    | forallE tt b => exact nomatch hrun
    | letE tt vv b => exact nomatch hrun
    | lit l => exact nomatch hrun
    | proj sp i e => exact nomatch hrun
  dsimp only at hrun
  obtain ⟨iv, hout, hres⟩ := bind_okB hrun
  injection hres with hres
  cases stk with
  | nil =>
    exact absurd hlen (by simp; omega)
  | cons u rest =>
    have hkeq : d + (k - 1) + 1 = d + k := by omega
    refine ⟨max F 2, ?_⟩
    rw [inferTypeCore_mono (Nat.le_max_left F 2) hbt, okB_bind]
    show (ensureSort (pureFns mode eager env (max F 2)) env (d + (k - 1) + 1)
        bt >>= fun v' => inferPisWrap (pureFns mode eager env (max F 2)) env d rest
          ((k - 1) - 1) (.sort (.imax u v'))) = _
    rw [ensureSort_def, ensureSortCore_eq, hkeq]
    rw [whnf_mono (Nat.le_max_left F 2) hww, okB_bind]
    dsimp only
    rw [pure_bind]
    unfold inferPisOut at hout
    rw [inferPisWrap_sort rest ((k - 1) - 1) (.imax u v)
      (Nat.le_max_right F 2), hout]
    rw [← hres]
    rfl

/-- A successful ∀-peel run is reproduced by the chained inference of
the bulk-opened residual followed by the chained tails, at some fuel. -/
theorem inferPis_sound {d : Nat} :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List Level) (F : Nat) (res : Expr),
      stk.length = k → 1 ≤ k →
      inferPis (pureFns mode eager env F) d fuel t k fvs stk = .ok res →
      ∃ F', (inferTypeCore mode eager env F' (d + k) (t.instantiateList fvs) >>=
        fun bt => inferPisWrap (pureFns mode eager env F') env d stk
          (k - 1) bt) = .ok res := by
  intro fuel
  induction fuel with
  | zero =>
    intro t k fvs stk F res hlen hk hrun
    rw [inferPis_zero] at hrun
    exact inferPisLeaf_sound hlen hk hrun
  | succ fuel ihf =>
    intro t k fvs stk F res hlen hk hrun
    by_cases hpi : ∃ ty body, t = Expr.forallE ty body
    · obtain ⟨ty, body, rfl⟩ := hpi
      rw [inferPis_succ_pi] at hrun
      obtain ⟨tty, htty, hrun⟩ := bind_okB hrun
      rw [infer_def] at htty
      obtain ⟨w, hww, hrun⟩ := bind_okB hrun
      rw [whnf_def] at hww
      obtain ⟨u, rfl⟩ : ∃ u, w = Expr.sort u := by
        cases w with
        | sort u' => exact ⟨u', rfl⟩
        | bvar i => exact nomatch hrun
        | fvar idx tt => exact nomatch hrun
        | const nm us => exact nomatch hrun
        | app f a => exact nomatch hrun
        | lam tt b => exact nomatch hrun
        | forallE tt b => exact nomatch hrun
        | letE tt vv b => exact nomatch hrun
        | lit l => exact nomatch hrun
        | proj sp i e => exact nomatch hrun
      dsimp only at hrun
      obtain ⟨F', hchain⟩ := ihf body (k + 1) _ _ F res
        (by simpa using hlen) (by omega) hrun
      obtain ⟨bt, hbt, hwrap⟩ := bind_okB hchain
      have hpiL : (Expr.forallE ty body).instantiateList fvs
          = Expr.forallE (ty.instantiateList fvs)
            (body.instantiateList fvs 1) := by
        simp [Expr.instantiateList]
      refine ⟨(max F F') + 1, ?_⟩
      rw [hpiL, inferTypeCore_forallE_eq]
      rw [inferTypeCore_mono (Nat.le_max_left F F') htty, okB_bind]
      rw [whnf_mono (Nat.le_max_left F F') hww, okB_bind]
      dsimp only
      rw [show (body.instantiateList fvs 1).instantiate1
          (.fvar (d + k) (ty.instantiateList fvs))
          = body.instantiateList
            (Expr.fvar (d + k) (ty.instantiateList fvs) :: fvs) from
        (Expr.instantiateList_cons ..).symm]
      rw [show d + k + 1 = d + (k + 1) from by omega]
      rw [inferTypeCore_mono (Nat.le_max_right F F') hbt, okB_bind]
      -- the chained level's `ensureSort` + `imax` is the wrap's head
      -- step (at `(k+1) - 1 = k`), and the suffix continues
      rw [show (k + 1 : Nat) - 1 = k from rfl] at hwrap
      unfold inferPisWrap at hwrap
      obtain ⟨v, hv, hwrap⟩ := bind_okB hwrap
      rw [ensureSort_def] at hv
      rw [show d + k + 1 = d + (k + 1) from by omega] at hv
      rw [ensureSortCore_mono (Nat.le_max_right F F') hv, okB_bind]
      try dsimp only
      try rw [pure_bind]
      exact inferPisWrap_mono (Nat.le_trans (Nat.le_max_right F F')
        (Nat.le_succ _)) hwrap
    · have ht : ∀ ty body, t ≠ Expr.forallE ty body :=
        fun ty b hh => hpi ⟨ty, b, hh⟩
      rw [inferPis_succ_ne_pi _ ht] at hrun
      exact inferPisLeaf_sound hlen hk hrun

end InferSound

end ConLeche
