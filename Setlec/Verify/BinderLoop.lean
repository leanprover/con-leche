import Setlec.Verify.BetaSpine
import Setlec.Verify.Abstract
import Setlec.Verify.AbstractRange
import Setlec.Verify.InferLeaves
import Setlec.Verify.Leaves

/-!
# Binder-telescope loops and their identification with the chained
bodies (task #72; task #100 stage 6 shapes)

The interned twins' binder cases (`annotatePisI`/`annotateLamsI`/
`inferLamsI`/`inferPisI`, `Setlec/Kernel/CoreI.lean`) peel a whole
binder telescope in one loop — bulk-opening with an fvar accumulator,
substituting only each binder's domain on the way in, and rebuilding
with one `abstractRange` per domain and one over the leaf.  This file
provides the pure mirrors (generic over the core record, like
`BetaSpine`'s) and proves the **soundness of each loop against the
chained spec**: a successful mirror run at the pure fueled knot is
reproduced by the original one-binder-at-a-time body at some fuel
(`inferLams_sound`, `inferPis_sound`, `annotatePis_sound`,
`annotateLams_sound`).  The interned walks
(`Setlec/Verify/BinderLoopI.lean`) compose their simulation against
the mirrors with these theorems, so the `Expr`-level specification —
and everything above it — is unchanged.

Post-erasure (task #100 stage 6) the loops are far simpler than their
task-#72 ancestors: the annotation pass computes nothing at binders,
the λ-rule has no body-type re-check, and the ∀-rule infers its
codomain sort — so every *rebuild* phase is a pure fold (no knot
calls), and the only reproduction obligations are the peel phase's
domain checks, the leaf runs, and — for the ∀-loop — the chained
rule's per-level `ensureSort` on an already-built sort (`whnf_sort`).
The rebuild/chain identification is the pure `abstractRange`/
`abstract1` algebra (`abstractRange_succ`).
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Setlec

variable {mode : CheckMode}

open Expr

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## The pure mirrors -/

/-- Mirror stack entry of `inferLamsI`: binder name, opened domain,
binder meta. -/
abbrev InferLamEntryX := Name × Expr × BinderMeta

/-- Mirror stack entry of the annotation loops: binder name, annotated
opened domain, binder info. -/
abbrev AnnotBinderEntryX := Name × Expr × BinderInfo

/-- Pure mirror of `inferLamsOutI` (a pure rebuild fold). -/
def inferLamsOut (d : Nat) :
    List InferLamEntryX → Nat → Expr → m Expr
  | [], _j, cur => pure cur
  | (n, tyo, mb) :: rest, j, cur =>
    inferLamsOut d rest (j - 1)
      (Expr.forallE n (tyo.abstractRange d j) cur mb)

/-- Pure mirror of `inferLamsLeafI`. -/
def inferLamsLeaf (r : CoreFns m) (d : Nat) (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List InferLamEntryX) : m Expr := do
  let bt ← r.infer (d + k) (t.instantiateList fvs)
  inferLamsOut d stk (k - 1) (bt.abstractRange d k)

/-- Pure mirror of `inferLamsI`. -/
def inferLams (r : CoreFns m) (d : Nat) :
    Nat → Expr → Nat → List Expr → List InferLamEntryX → m Expr
  | fuel + 1, t, k, fvs, stk =>
    match t with
    | .lam n ty body mb => do
      let tyo := ty.instantiateList fvs
      let tty ← r.infer (d + k) tyo
      match ← r.whnf (d + k) tty with
      | .sort _ =>
        inferLams r d fuel body (k + 1) (Expr.fvar (d + k) n tyo :: fvs)
          ((n, tyo, mb) :: stk)
      | _ => throw (.invalid "expected a sort")
    | t => inferLamsLeaf r d t k fvs stk
  | 0, t, k, fvs, stk => inferLamsLeaf r d t k fvs stk

/-- Pure mirror of `inferPisOutI` (the `imax` fold, pure). -/
def inferPisOut : List Level → Level → Level
  | [], v => v
  | u :: rest, v => inferPisOut rest (.imax u v)

/-- Pure mirror of `inferPisLeafI`. -/
def inferPisLeaf (r : CoreFns m) (d : Nat) (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List Level) : m Expr := do
  let bt ← r.infer (d + k) (t.instantiateList fvs)
  match ← r.whnf (d + k) bt with
  | .sort v => pure (Expr.sort (inferPisOut stk v))
  | _ => throw (.invalid "expected a sort")

/-- Pure mirror of `inferPisI`. -/
def inferPis (r : CoreFns m) (d : Nat) :
    Nat → Expr → Nat → List Expr → List Level → m Expr
  | fuel + 1, t, k, fvs, stk =>
    match t with
    | .forallE n ty body _mb => do
      let tyo := ty.instantiateList fvs
      let tty ← r.infer (d + k) tyo
      match ← r.whnf (d + k) tty with
      | .sort u =>
        inferPis r d fuel body (k + 1) (Expr.fvar (d + k) n tyo :: fvs)
          (u :: stk)
      | _ => throw (.invalid "expected a sort")
    | t => inferPisLeaf r d t k fvs stk
  | 0, t, k, fvs, stk => inferPisLeaf r d t k fvs stk

/-- Pure mirror of `annotateBindersOutI` (a pure rebuild fold, generic
in the rebuilt binder kind). -/
def annotateBindersOut (mk : Name → Expr → Expr → BinderInfo → Expr)
    (d : Nat) :
    List AnnotBinderEntryX → Nat → Expr → m Expr
  | [], _j, cur => pure cur
  | (n, ty', bi) :: rest, j, cur =>
    annotateBindersOut mk d rest (j - 1)
      (mk n (ty'.abstractRange d j) cur bi)

/-- Pure mirror of `annotatePisLeafI`. -/
def annotatePisLeaf (r : CoreFns m) (d : Nat) (t : Expr)
    (k : Nat) (fvs : List Expr) (stk : List AnnotBinderEntryX) : m Expr := do
  let leaf' ← r.annotate (d + k) (t.instantiateList fvs)
  annotateBindersOut (fun n ty b bi => .forallE n ty b ⟨bi⟩) d
    stk (k - 1) (leaf'.abstractRange d k)

/-- Pure mirror of `annotatePisI`. -/
def annotatePis (r : CoreFns m) (d : Nat) :
    Nat → Expr → Nat → List Expr → List AnnotBinderEntryX → m Expr
  | fuel + 1, t, k, fvs, stk =>
    match t with
    | .forallE n ty body mb => do
      let ty' ← r.annotate (d + k) (ty.instantiateList fvs)
      annotatePis r d fuel body (k + 1)
        (Expr.fvar (d + k) n ty' :: fvs) ((n, ty', mb.bi) :: stk)
    | t => annotatePisLeaf r d t k fvs stk
  | 0, t, k, fvs, stk => annotatePisLeaf r d t k fvs stk

/-- Pure mirror of `annotateLamsLeafI`. -/
def annotateLamsLeaf (r : CoreFns m) (d : Nat) (t : Expr)
    (k : Nat) (fvs : List Expr) (stk : List AnnotBinderEntryX) : m Expr := do
  let leaf' ← r.annotate (d + k) (t.instantiateList fvs)
  annotateBindersOut (fun n ty b bi => .lam n ty b ⟨bi⟩) d
    stk (k - 1) (leaf'.abstractRange d k)

/-- Pure mirror of `annotateLamsI`. -/
def annotateLams (r : CoreFns m) (d : Nat) :
    Nat → Expr → Nat → List Expr → List AnnotBinderEntryX → m Expr
  | fuel + 1, t, k, fvs, stk =>
    match t with
    | .lam n ty body mb => do
      let ty' ← r.annotate (d + k) (ty.instantiateList fvs)
      annotateLams r d fuel body (k + 1)
        (Expr.fvar (d + k) n ty' :: fvs) ((n, ty', mb.bi) :: stk)
    | t => annotateLamsLeaf r d t k fvs stk
  | 0, t, k, fvs, stk => annotateLamsLeaf r d t k fvs stk

/-! ## The chained tails (wraps) -/

/-- The chained `inferBody` λ-tail folded over the peeled binders
(innermost first, `j` the head entry's binder level): post-erasure the
λ-rule performs no runs after the body inference, so the tail is a pure
`abstract1` fold. -/
def inferLamsWrap (d : Nat) :
    List InferLamEntryX → Nat → Expr → m Expr
  | [], _j, bt => pure bt
  | (n, tyo, mb) :: rest, j, bt =>
    inferLamsWrap d rest (j - 1)
      (.forallE n tyo (bt.abstract1 (d + j)) mb)

/-- The chained `inferBody` ∀-tail folded over the peeled binders: per
level, the chained rule's `ensureSort` of the freshly built inner sort
(reproduced by `whnf_sort`), then the `imax`. -/
def inferPisWrap (r : CoreFns m) (env : Env) (d : Nat) :
    List Level → Nat → Expr → m Expr
  | [], _j, bt => pure bt
  | u :: rest, j, bt => do
    let v ← ensureSort r env (d + j + 1) bt
    inferPisWrap r env d rest (j - 1) (.sort (.imax u v))

/-- The chained `annotateBody` ∀-tail folded over the peeled binders
(pure: the annotation pass computes nothing at binders). -/
def annotatePisWrap (d : Nat) :
    List AnnotBinderEntryX → Nat → Expr → m Expr
  | [], _j, body' => pure body'
  | (n, ty', bi) :: rest, j, body' =>
    annotatePisWrap d rest (j - 1)
      (.forallE n ty' (body'.abstract1 (d + j)) ⟨bi⟩)

/-- The chained `annotateBody` λ-tail folded over the peeled binders. -/
def annotateLamsWrap (d : Nat) :
    List AnnotBinderEntryX → Nat → Expr → m Expr
  | [], _j, body' => pure body'
  | (n, ty', bi) :: rest, j, body' =>
    annotateLamsWrap d rest (j - 1)
      (.lam n ty' (body'.abstract1 (d + j)) ⟨bi⟩)

/-! ## Unfolding equations -/

section Unfold

variable {r : CoreFns m} {env : Env} {d : Nat}

theorem inferLams_zero (t : Expr) (k : Nat) (fvs : List Expr)
    (stk : List InferLamEntryX) :
    inferLams r d 0 t k fvs stk = inferLamsLeaf r d t k fvs stk := rfl

theorem inferLams_succ_lam (fuel : Nat) (n : Name) (ty body : Expr)
    (mb : BinderMeta) (k : Nat) (fvs : List Expr)
    (stk : List InferLamEntryX) :
    inferLams r d (fuel + 1) (.lam n ty body mb) k fvs stk
      = (do
        let tty ← r.infer (d + k) (ty.instantiateList fvs)
        match ← r.whnf (d + k) tty with
        | .sort _ =>
          inferLams r d fuel body (k + 1)
            (Expr.fvar (d + k) n (ty.instantiateList fvs) :: fvs)
            ((n, ty.instantiateList fvs, mb) :: stk)
        | _ => throw (.invalid "expected a sort")) := rfl

theorem inferLams_succ_ne_lam (fuel : Nat) {t : Expr}
    (ht : ∀ n ty body mb, t ≠ .lam n ty body mb) (k : Nat)
    (fvs : List Expr) (stk : List InferLamEntryX) :
    inferLams r d (fuel + 1) t k fvs stk
      = inferLamsLeaf r d t k fvs stk := by
  cases t with
  | lam n ty body mb => exact absurd rfl (ht n ty body mb)
  | _ => rw [inferLams] <;> exact fun _ _ _ _ h => nomatch h

theorem inferPis_zero (t : Expr) (k : Nat) (fvs : List Expr)
    (stk : List Level) :
    inferPis r d 0 t k fvs stk = inferPisLeaf r d t k fvs stk := rfl

theorem inferPis_succ_pi (fuel : Nat) (n : Name) (ty body : Expr)
    (mb : BinderMeta) (k : Nat) (fvs : List Expr)
    (stk : List Level) :
    inferPis r d (fuel + 1) (.forallE n ty body mb) k fvs stk
      = (do
        let tty ← r.infer (d + k) (ty.instantiateList fvs)
        match ← r.whnf (d + k) tty with
        | .sort u =>
          inferPis r d fuel body (k + 1)
            (Expr.fvar (d + k) n (ty.instantiateList fvs) :: fvs)
            (u :: stk)
        | _ => throw (.invalid "expected a sort")) := rfl

theorem inferPis_succ_ne_pi (fuel : Nat) {t : Expr}
    (ht : ∀ n ty body mb, t ≠ .forallE n ty body mb) (k : Nat)
    (fvs : List Expr) (stk : List Level) :
    inferPis r d (fuel + 1) t k fvs stk
      = inferPisLeaf r d t k fvs stk := by
  cases t with
  | forallE n ty body mb => exact absurd rfl (ht n ty body mb)
  | _ => rw [inferPis] <;> exact fun _ _ _ _ h => nomatch h

omit [MonadExceptOf CheckError m] in
theorem annotatePis_zero (t : Expr) (k : Nat) (fvs : List Expr)
    (stk : List AnnotBinderEntryX) :
    annotatePis r d 0 t k fvs stk = annotatePisLeaf r d t k fvs stk := rfl

omit [MonadExceptOf CheckError m] in
theorem annotatePis_succ_pi (fuel : Nat) (n : Name) (ty body : Expr)
    (mb : BinderMeta) (k : Nat) (fvs : List Expr)
    (stk : List AnnotBinderEntryX) :
    annotatePis r d (fuel + 1) (.forallE n ty body mb) k fvs stk
      = (do
        let ty' ← r.annotate (d + k) (ty.instantiateList fvs)
        annotatePis r d fuel body (k + 1)
          (Expr.fvar (d + k) n ty' :: fvs) ((n, ty', mb.bi) :: stk)) := rfl

omit [MonadExceptOf CheckError m] in
theorem annotatePis_succ_ne_pi (fuel : Nat) {t : Expr}
    (ht : ∀ n ty body mb, t ≠ .forallE n ty body mb) (k : Nat)
    (fvs : List Expr) (stk : List AnnotBinderEntryX) :
    annotatePis r d (fuel + 1) t k fvs stk
      = annotatePisLeaf r d t k fvs stk := by
  cases t with
  | forallE n ty body mb => exact absurd rfl (ht n ty body mb)
  | _ => rw [annotatePis] <;> exact fun _ _ _ _ h => nomatch h

omit [MonadExceptOf CheckError m] in
theorem annotateLams_zero (t : Expr) (k : Nat) (fvs : List Expr)
    (stk : List AnnotBinderEntryX) :
    annotateLams r d 0 t k fvs stk = annotateLamsLeaf r d t k fvs stk := rfl

omit [MonadExceptOf CheckError m] in
theorem annotateLams_succ_lam (fuel : Nat) (n : Name) (ty body : Expr)
    (mb : BinderMeta) (k : Nat) (fvs : List Expr)
    (stk : List AnnotBinderEntryX) :
    annotateLams r d (fuel + 1) (.lam n ty body mb) k fvs stk
      = (do
        let ty' ← r.annotate (d + k) (ty.instantiateList fvs)
        annotateLams r d fuel body (k + 1)
          (Expr.fvar (d + k) n ty' :: fvs) ((n, ty', mb.bi) :: stk)) := rfl

omit [MonadExceptOf CheckError m] in
theorem annotateLams_succ_ne_lam (fuel : Nat) {t : Expr}
    (ht : ∀ n ty body mb, t ≠ .lam n ty body mb) (k : Nat)
    (fvs : List Expr) (stk : List AnnotBinderEntryX) :
    annotateLams r d (fuel + 1) t k fvs stk
      = annotateLamsLeaf r d t k fvs stk := by
  cases t with
  | lam n ty body mb => exact absurd rfl (ht n ty body mb)
  | _ => rw [annotateLams] <;> exact fun _ _ _ _ h => nomatch h

/-! Shape equations of the fueled bodies on binder nodes (definitional;
the fuel steps once). -/

theorem inferTypeCore_forallE_eq (env : Env) (F d : Nat) (n : Name)
    (ty body : Expr) (mb : BinderMeta) :
    inferTypeCore mode env (F + 1) d (.forallE n ty body mb)
      = (inferTypeCore mode env F d ty >>= fun tty =>
         whnf mode env F d tty >>= fun w =>
         match w with
         | .sort u =>
           inferTypeCore mode env F (d + 1)
               (body.instantiate1 (.fvar d n ty)) >>= fun bt =>
             ensureSortCore mode env F (d + 1) bt >>= fun v =>
               pure (Expr.sort (.imax u v))
         | _ => throw (.invalid "expected a sort")) := rfl

theorem inferTypeCore_lam_eq (env : Env) (F d : Nat) (n : Name)
    (ty body : Expr) (mb : BinderMeta) :
    inferTypeCore mode env (F + 1) d (.lam n ty body mb)
      = (inferTypeCore mode env F d ty >>= fun tty =>
         whnf mode env F d tty >>= fun w =>
         match w with
         | .sort _ =>
           inferTypeCore mode env F (d + 1)
               (body.instantiate1 (.fvar d n ty)) >>= fun bt =>
             pure (Expr.forallE n ty (bt.abstract1 d) mb)
         | _ => throw (.invalid "expected a sort")) := rfl

theorem annotateCore_forallE_eq (env : Env) (F d : Nat) (n : Name)
    (ty body : Expr) (mb : BinderMeta) :
    annotateCore mode env (F + 1) d (.forallE n ty body mb)
      = (annotateCore mode env F d ty >>= fun ty' =>
         annotateCore mode env F (d + 1)
             (body.instantiate1 (.fvar d n ty')) >>= fun body' =>
           pure (Expr.forallE n ty' (body'.abstract1 d) ⟨mb.bi⟩)) := rfl

theorem annotateCore_lam_eq (env : Env) (F d : Nat) (n : Name)
    (ty body : Expr) (mb : BinderMeta) :
    annotateCore mode env (F + 1) d (.lam n ty body mb)
      = (annotateCore mode env F d ty >>= fun ty' =>
         annotateCore mode env F (d + 1)
             (body.instantiate1 (.fvar d n ty')) >>= fun body' =>
           pure (Expr.lam n ty' (body'.abstract1 d) ⟨mb.bi⟩)) := rfl

theorem ensureSortCore_eq (env : Env) (F d : Nat) (e : Expr) :
    ensureSortCore mode env F d e
      = (whnf mode env F d e >>= fun w =>
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
    whnf mode env (F + 2) d (.sort u) = .ok (.sort u) := by
  -- one iteration of the reduction loop suffices (task #106: the step
  -- budget is `irreducible`, so peel it with its positivity witness)
  obtain ⟨k, hk⟩ := whnfLoopFuel_succ
  rw [whnf_succ]
  show whnfLoop (pureFns mode env (F + 1)) env d whnfLoopFuel _ = _
  rw [hk]
  rfl

end Unfold

/-! ## Fixed-fuel (`atF`) spellings -/

section AtF

variable {env : Env}

theorem inferLamsOut_atF (d : Nat) :
    ∀ (stk : List InferLamEntryX) (j : Nat) (cur : Expr) (F : Nat),
      (inferLamsOut (m := FueledM) d stk j cur).val F
        = inferLamsOut (m := CheckM) d stk j cur
  | [], _, _, _ => rfl
  | (_n, _tyo, _mb) :: rest, j, _cur, F =>
    inferLamsOut_atF d rest (j - 1) _ F

theorem inferLamsLeaf_atF (d : Nat) (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List InferLamEntryX) (F : Nat) :
    (inferLamsLeaf (fueledFns mode env) d t k fvs stk).val F
      = inferLamsLeaf (pureFns mode env F) d t k fvs stk := by
  unfold inferLamsLeaf
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  exact inferLamsOut_atF d stk (k - 1) _ F

theorem inferLams_atF (d : Nat) :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List InferLamEntryX) (F : Nat),
      (inferLams (fueledFns mode env) d fuel t k fvs stk).val F
        = inferLams (pureFns mode env F) d fuel t k fvs stk
  | 0, t, k, fvs, stk, F => inferLamsLeaf_atF d t k fvs stk F
  | fuel + 1, t, k, fvs, stk, F => by
    by_cases hlam : ∃ n ty body mb, t = Expr.lam n ty body mb
    · obtain ⟨n, ty, body, mb, rfl⟩ := hlam
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
    · have ht : ∀ n ty body mb, t ≠ Expr.lam n ty body mb :=
        fun n ty b mb hh => hlam ⟨n, ty, b, mb, hh⟩
      rw [inferLams_succ_ne_lam _ ht, inferLams_succ_ne_lam _ ht]
      exact inferLamsLeaf_atF d t k fvs stk F

theorem inferPisLeaf_atF (d : Nat) (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List Level) (F : Nat) :
    (inferPisLeaf (fueledFns mode env) d t k fvs stk).val F
      = inferPisLeaf (pureFns mode env F) d t k fvs stk := by
  unfold inferPisLeaf
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  rw [FueledM.atF_bind]
  congr 1
  funext w
  cases w <;> rfl

theorem inferPis_atF (d : Nat) :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List Level) (F : Nat),
      (inferPis (fueledFns mode env) d fuel t k fvs stk).val F
        = inferPis (pureFns mode env F) d fuel t k fvs stk
  | 0, t, k, fvs, stk, F => inferPisLeaf_atF d t k fvs stk F
  | fuel + 1, t, k, fvs, stk, F => by
    by_cases hpi : ∃ n ty body mb, t = Expr.forallE n ty body mb
    · obtain ⟨n, ty, body, mb, rfl⟩ := hpi
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
    · have ht : ∀ n ty body mb, t ≠ Expr.forallE n ty body mb :=
        fun n ty b mb hh => hpi ⟨n, ty, b, mb, hh⟩
      rw [inferPis_succ_ne_pi _ ht, inferPis_succ_ne_pi _ ht]
      exact inferPisLeaf_atF d t k fvs stk F

theorem annotateBindersOut_atF (mk : Name → Expr → Expr → BinderInfo → Expr)
    (d : Nat) :
    ∀ (stk : List AnnotBinderEntryX) (j : Nat) (cur : Expr) (F : Nat),
      (annotateBindersOut (m := FueledM) mk d stk j cur).val F
        = annotateBindersOut (m := CheckM) mk d stk j cur
  | [], _, _, _ => rfl
  | (_n, _ty', _bi) :: rest, j, _cur, F =>
    annotateBindersOut_atF mk d rest (j - 1) _ F

theorem annotatePisLeaf_atF (d : Nat) (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List AnnotBinderEntryX) (F : Nat) :
    (annotatePisLeaf (fueledFns mode env) d t k fvs stk).val F
      = annotatePisLeaf (pureFns mode env F) d t k fvs stk := by
  unfold annotatePisLeaf
  rw [FueledM.atF_bind]
  congr 1
  funext leaf'
  exact annotateBindersOut_atF _ d stk (k - 1) _ F

theorem annotatePis_atF (d : Nat) :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List AnnotBinderEntryX) (F : Nat),
      (annotatePis (fueledFns mode env) d fuel t k fvs stk).val F
        = annotatePis (pureFns mode env F) d fuel t k fvs stk
  | 0, t, k, fvs, stk, F => annotatePisLeaf_atF d t k fvs stk F
  | fuel + 1, t, k, fvs, stk, F => by
    by_cases hpi : ∃ n ty body mb, t = Expr.forallE n ty body mb
    · obtain ⟨n, ty, body, mb, rfl⟩ := hpi
      rw [annotatePis_succ_pi, annotatePis_succ_pi]
      rw [FueledM.atF_bind]
      congr 1
      funext ty'
      exact annotatePis_atF d fuel body (k + 1) _ _ F
    · have ht : ∀ n ty body mb, t ≠ Expr.forallE n ty body mb :=
        fun n ty b mb hh => hpi ⟨n, ty, b, mb, hh⟩
      rw [annotatePis_succ_ne_pi _ ht, annotatePis_succ_ne_pi _ ht]
      exact annotatePisLeaf_atF d t k fvs stk F

theorem annotateLamsLeaf_atF (d : Nat) (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List AnnotBinderEntryX) (F : Nat) :
    (annotateLamsLeaf (fueledFns mode env) d t k fvs stk).val F
      = annotateLamsLeaf (pureFns mode env F) d t k fvs stk := by
  unfold annotateLamsLeaf
  rw [FueledM.atF_bind]
  congr 1
  funext leaf'
  exact annotateBindersOut_atF _ d stk (k - 1) _ F

theorem annotateLams_atF (d : Nat) :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List AnnotBinderEntryX) (F : Nat),
      (annotateLams (fueledFns mode env) d fuel t k fvs stk).val F
        = annotateLams (pureFns mode env F) d fuel t k fvs stk
  | 0, t, k, fvs, stk, F => annotateLamsLeaf_atF d t k fvs stk F
  | fuel + 1, t, k, fvs, stk, F => by
    by_cases hlam : ∃ n ty body mb, t = Expr.lam n ty body mb
    · obtain ⟨n, ty, body, mb, rfl⟩ := hlam
      rw [annotateLams_succ_lam, annotateLams_succ_lam]
      rw [FueledM.atF_bind]
      congr 1
      funext ty'
      exact annotateLams_atF d fuel body (k + 1) _ _ F
    · have ht : ∀ n ty body mb, t ≠ Expr.lam n ty body mb :=
        fun n ty b mb hh => hlam ⟨n, ty, b, mb, hh⟩
      rw [annotateLams_succ_ne_lam _ ht, annotateLams_succ_ne_lam _ ht]
      exact annotateLamsLeaf_atF d t k fvs stk F

end AtF

/-! ## Rebuild/wrap identification (pure) and peel soundness -/

section InferSound

variable {env : Env}

/-- The rebuild fold equals the chained `abstract1` fold — pure
`abstractRange` algebra (`abstractRange_succ`), stated at the rebuild
cursor the leaf phase enters with (`stk.length = j + 1`). -/
theorem inferLamsOut_wrap {d : Nat} :
    ∀ (stk : List InferLamEntryX) (j : Nat) (bt : Expr),
      stk.length = j + 1 →
      inferLamsOut (m := CheckM) d stk j (bt.abstractRange d (j + 1))
        = inferLamsWrap (m := CheckM) d stk j bt := by
  intro stk
  induction stk with
  | nil => intro j bt hlen; exact nomatch hlen
  | cons e rest ih =>
    obtain ⟨n, tyo, mb⟩ := e
    intro j bt hlen
    show inferLamsOut (m := CheckM) d rest (j - 1)
        (Expr.forallE n (tyo.abstractRange d j)
          (bt.abstractRange d (j + 1)) mb)
      = inferLamsWrap (m := CheckM) d rest (j - 1)
          (Expr.forallE n tyo (bt.abstract1 (d + j)) mb)
    cases rest with
    | nil =>
      obtain rfl : j = 0 := by simpa using hlen
      show Except.ok _ = Except.ok _
      congr 2
      · exact abstractRange_zero ..
      · rw [abstractRange_succ, abstractRange_zero]
    | cons e' rest' =>
      have hj1 : 1 ≤ j := by
        simp only [List.length_cons] at hlen
        omega
      have hnode : Expr.forallE n (tyo.abstractRange d j)
          (bt.abstractRange d (j + 1)) mb
          = (Expr.forallE n tyo (bt.abstract1 (d + j)) mb).abstractRange
              d ((j - 1) + 1) := by
        have hj : (j - 1) + 1 = j := by omega
        rw [hj]
        show _ = Expr.forallE n (tyo.abstractRange d j 0)
          ((bt.abstract1 (d + j) 0).abstractRange d j 1) mb
        rw [abstractRange_succ]
      rw [hnode]
      exact ih (j - 1) _ (by
        simp only [List.length_cons] at hlen ⊢
        omega)

/-- Leaf-phase soundness: the mirror's leaf run is the chained
inference of the bulk-opened residual followed by the (pure) tails. -/
theorem inferLamsLeaf_sound {d : Nat} {t : Expr}
    {k : Nat} {fvs : List Expr} {stk : List InferLamEntryX} {F : Nat}
    {res : Expr}
    (hlen : stk.length = k)
    (hrun : inferLamsLeaf (pureFns mode env F) d t k fvs stk = .ok res) :
    ∃ F', (inferTypeCore mode env F' (d + k) (t.instantiateList fvs) >>=
      fun bt => inferLamsWrap (m := CheckM) d stk (k - 1) bt)
        = .ok res := by
  unfold inferLamsLeaf at hrun
  obtain ⟨bt, hbt, hrun⟩ := bind_okB hrun
  rw [infer_def] at hbt
  cases stk with
  | nil =>
    obtain rfl : k = 0 := by simpa using hlen.symm
    unfold inferLamsOut at hrun
    rw [abstractRange_zero] at hrun
    exact ⟨F, by rw [hbt, okB_bind]; exact hrun⟩
  | cons e rest =>
    have hk1 : 1 ≤ k := by rw [← hlen]; simp
    have hkeq : (k - 1) + 1 = k := by omega
    refine ⟨F, ?_⟩
    rw [hbt, okB_bind]
    rw [← inferLamsOut_wrap (e :: rest) (k - 1) bt
      (by simp only [List.length_cons] at hlen ⊢; omega)]
    rw [hkeq]
    exact hrun

/-- A successful peel run is reproduced by the chained inference of the
bulk-opened residual followed by the chained tails, at some fuel. -/
theorem inferLams_sound {d : Nat} :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List InferLamEntryX) (F : Nat) (res : Expr),
      stk.length = k →
      inferLams (pureFns mode env F) d fuel t k fvs stk = .ok res →
      ∃ F', (inferTypeCore mode env F' (d + k) (t.instantiateList fvs) >>=
        fun bt => inferLamsWrap (m := CheckM) d stk (k - 1) bt)
          = .ok res := by
  intro fuel
  induction fuel with
  | zero =>
    intro t k fvs stk F res hlen hrun
    rw [inferLams_zero] at hrun
    exact inferLamsLeaf_sound hlen hrun
  | succ fuel ihf =>
    intro t k fvs stk F res hlen hrun
    by_cases hlam : ∃ n ty body mb, t = Expr.lam n ty body mb
    · obtain ⟨n, ty, body, mb, rfl⟩ := hlam
      rw [inferLams_succ_lam] at hrun
      obtain ⟨tty, htty, hrun⟩ := bind_okB hrun
      rw [infer_def] at htty
      obtain ⟨w, hww, hrun⟩ := bind_okB hrun
      rw [whnf_def] at hww
      obtain ⟨u, rfl⟩ : ∃ u, w = Expr.sort u := by
        cases w with
        | sort u' => exact ⟨u', rfl⟩
        | bvar i => exact nomatch hrun
        | fvar idx nm tt => exact nomatch hrun
        | const nm us => exact nomatch hrun
        | app f a => exact nomatch hrun
        | lam nm tt b mm => exact nomatch hrun
        | forallE nm tt b mm => exact nomatch hrun
        | letE nm tt vv b => exact nomatch hrun
        | lit l => exact nomatch hrun
        | proj sp i e => exact nomatch hrun
      dsimp only at hrun
      obtain ⟨F', hchain⟩ := ihf body (k + 1) _ _ F res
        (by simpa using hlen) hrun
      obtain ⟨bt, hbt, hwrap⟩ := bind_okB hchain
      have hlamL : (Expr.lam n ty body mb).instantiateList fvs
          = Expr.lam n (ty.instantiateList fvs)
            (body.instantiateList fvs 1) mb := by
        simp [Expr.instantiateList]
      refine ⟨(max F F') + 1, ?_⟩
      rw [hlamL, inferTypeCore_lam_eq]
      rw [inferTypeCore_mono (Nat.le_max_left F F') htty, okB_bind]
      rw [whnf_mono (Nat.le_max_left F F') hww, okB_bind]
      dsimp only
      rw [show (body.instantiateList fvs 1).instantiate1
          (.fvar (d + k) n (ty.instantiateList fvs))
          = body.instantiateList
            (Expr.fvar (d + k) n (ty.instantiateList fvs) :: fvs) from
        (Expr.instantiateList_cons ..).symm]
      rw [show d + k + 1 = d + (k + 1) from by omega]
      rw [inferTypeCore_mono (Nat.le_max_right F F') hbt, okB_bind, pure_bind]
      -- the wrap's head step is definitional
      rw [show (k + 1 : Nat) - 1 = k from rfl] at hwrap
      exact hwrap
    · have ht : ∀ n ty body mb, t ≠ Expr.lam n ty body mb :=
        fun n ty b mb hh => hlam ⟨n, ty, b, mb, hh⟩
      rw [inferLams_succ_ne_lam _ ht] at hrun
      exact inferLamsLeaf_sound hlen hrun

/-- The ∀-wrap is fuel monotone (its only runs are `ensureSort`s). -/
theorem inferPisWrap_mono {d : Nat} :
    ∀ {stk : List Level} {j : Nat} {bt : Expr} {F F' : Nat},
      F ≤ F' → ∀ {res : Expr},
      inferPisWrap (pureFns mode env F) env d stk j bt = .ok res →
      inferPisWrap (pureFns mode env F') env d stk j bt = .ok res := by
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

/-- The `imax`-fold wrap collapses on an explicit sort (the chained
per-level `ensureSort`s reduce by `whnf_sort`). -/
theorem inferPisWrap_sort {d : Nat} :
    ∀ (stk : List Level) (j : Nat) (v : Level) {F : Nat}, 2 ≤ F →
      inferPisWrap (pureFns mode env F) env d stk j (.sort v)
        = .ok (.sort (inferPisOut stk v)) := by
  intro stk
  induction stk with
  | nil => intro j v F hF; rfl
  | cons u rest ih =>
    intro j v F hF
    show (ensureSort (pureFns mode env F) env (d + j + 1) (.sort v) >>=
      fun v' => inferPisWrap (pureFns mode env F) env d rest (j - 1)
        (.sort (.imax u v'))) = _
    rw [ensureSort_def, ensureSortCore_eq]
    have hw : whnf mode env F (d + j + 1) (.sort v) = .ok (.sort v) := by
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
    (hrun : inferPisLeaf (pureFns mode env F) d t k fvs stk = .ok res) :
    ∃ F', (inferTypeCore mode env F' (d + k) (t.instantiateList fvs) >>=
      fun bt => inferPisWrap (pureFns mode env F') env d stk (k - 1) bt)
        = .ok res := by
  unfold inferPisLeaf at hrun
  obtain ⟨bt, hbt, hrun⟩ := bind_okB hrun
  rw [infer_def] at hbt
  obtain ⟨w, hww, hrun⟩ := bind_okB hrun
  rw [whnf_def] at hww
  obtain ⟨v, rfl⟩ : ∃ v, w = Expr.sort v := by
    cases w with
    | sort v' => exact ⟨v', rfl⟩
    | bvar i => exact nomatch hrun
    | fvar idx nm tt => exact nomatch hrun
    | const nm us => exact nomatch hrun
    | app f a => exact nomatch hrun
    | lam nm tt b mm => exact nomatch hrun
    | forallE nm tt b mm => exact nomatch hrun
    | letE nm tt vv b => exact nomatch hrun
    | lit l => exact nomatch hrun
    | proj sp i e => exact nomatch hrun
  injection hrun with hres
  cases stk with
  | nil =>
    exact absurd hlen (by simp; omega)
  | cons u rest =>
    have hkeq : d + (k - 1) + 1 = d + k := by omega
    refine ⟨max F 2, ?_⟩
    rw [inferTypeCore_mono (Nat.le_max_left F 2) hbt, okB_bind]
    show (ensureSort (pureFns mode env (max F 2)) env (d + (k - 1) + 1) bt >>=
      fun v' => inferPisWrap (pureFns mode env (max F 2)) env d rest
        ((k - 1) - 1) (.sort (.imax u v'))) = _
    rw [ensureSort_def, ensureSortCore_eq, hkeq]
    rw [whnf_mono (Nat.le_max_left F 2) hww, okB_bind]
    dsimp only
    rw [pure_bind]
    rw [inferPisWrap_sort rest ((k - 1) - 1) (.imax u v)
      (Nat.le_max_right F 2)]
    rw [← hres]
    rfl

/-- A successful ∀-peel run is reproduced by the chained inference of
the bulk-opened residual followed by the chained tails, at some fuel. -/
theorem inferPis_sound {d : Nat} :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List Level) (F : Nat) (res : Expr),
      stk.length = k → 1 ≤ k →
      inferPis (pureFns mode env F) d fuel t k fvs stk = .ok res →
      ∃ F', (inferTypeCore mode env F' (d + k) (t.instantiateList fvs) >>=
        fun bt => inferPisWrap (pureFns mode env F') env d stk (k - 1) bt)
          = .ok res := by
  intro fuel
  induction fuel with
  | zero =>
    intro t k fvs stk F res hlen hk hrun
    rw [inferPis_zero] at hrun
    exact inferPisLeaf_sound hlen hk hrun
  | succ fuel ihf =>
    intro t k fvs stk F res hlen hk hrun
    by_cases hpi : ∃ n ty body mb, t = Expr.forallE n ty body mb
    · obtain ⟨n, ty, body, mb, rfl⟩ := hpi
      rw [inferPis_succ_pi] at hrun
      obtain ⟨tty, htty, hrun⟩ := bind_okB hrun
      rw [infer_def] at htty
      obtain ⟨w, hww, hrun⟩ := bind_okB hrun
      rw [whnf_def] at hww
      obtain ⟨u, rfl⟩ : ∃ u, w = Expr.sort u := by
        cases w with
        | sort u' => exact ⟨u', rfl⟩
        | bvar i => exact nomatch hrun
        | fvar idx nm tt => exact nomatch hrun
        | const nm us => exact nomatch hrun
        | app f a => exact nomatch hrun
        | lam nm tt b mm => exact nomatch hrun
        | forallE nm tt b mm => exact nomatch hrun
        | letE nm tt vv b => exact nomatch hrun
        | lit l => exact nomatch hrun
        | proj sp i e => exact nomatch hrun
      dsimp only at hrun
      obtain ⟨F', hchain⟩ := ihf body (k + 1) _ _ F res
        (by simpa using hlen) (by omega) hrun
      obtain ⟨bt, hbt, hwrap⟩ := bind_okB hchain
      have hpiL : (Expr.forallE n ty body mb).instantiateList fvs
          = Expr.forallE n (ty.instantiateList fvs)
            (body.instantiateList fvs 1) mb := by
        simp [Expr.instantiateList]
      refine ⟨(max F F') + 1, ?_⟩
      rw [hpiL, inferTypeCore_forallE_eq]
      rw [inferTypeCore_mono (Nat.le_max_left F F') htty, okB_bind]
      rw [whnf_mono (Nat.le_max_left F F') hww, okB_bind]
      dsimp only
      rw [show (body.instantiateList fvs 1).instantiate1
          (.fvar (d + k) n (ty.instantiateList fvs))
          = body.instantiateList
            (Expr.fvar (d + k) n (ty.instantiateList fvs) :: fvs) from
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
      rw [ensureSortCore_mono (Nat.le_max_right F F') hv, okB_bind,
        pure_bind]
      exact inferPisWrap_mono (Nat.le_trans (Nat.le_max_right F F')
        (Nat.le_succ _)) hwrap
    · have ht : ∀ n ty body mb, t ≠ Expr.forallE n ty body mb :=
        fun n ty b mb hh => hpi ⟨n, ty, b, mb, hh⟩
      rw [inferPis_succ_ne_pi _ ht] at hrun
      exact inferPisLeaf_sound hlen hk hrun

end InferSound

/-! ## Annotation loops: rebuild/wrap identification and peel
soundness -/

section AnnotSound

variable {env : Env}

/-- The generic rebuild fold equals the chained `abstract1` fold
(instantiated at ∀- and λ-rebuilds; `hmk` is the constructor's
`abstractRange`/`abstract1` commutation, definitional for both). -/
theorem annotateBindersOut_wrap
    {mk : Name → Expr → Expr → BinderInfo → Expr}
    (hmkR : ∀ n ty b bi d k c, (mk n ty b bi).abstractRange d k c
      = mk n (ty.abstractRange d k c) (b.abstractRange d k (c + 1)) bi)
    {d : Nat}
    (wrap : List AnnotBinderEntryX → Nat → Expr → CheckM Expr)
    (hwrap_nil : ∀ j bt, wrap [] j bt = pure bt)
    (hwrap_cons : ∀ n ty' bi rest j bt,
      wrap ((n, ty', bi) :: rest) j bt
        = wrap rest (j - 1) (mk n ty' (bt.abstract1 (d + j)) bi)) :
    ∀ (stk : List AnnotBinderEntryX) (j : Nat) (bt : Expr),
      stk.length = j + 1 →
      annotateBindersOut (m := CheckM) mk d stk j
          (bt.abstractRange d (j + 1))
        = wrap stk j bt := by
  intro stk
  induction stk with
  | nil => intro j bt hlen; exact nomatch hlen
  | cons e rest ih =>
    obtain ⟨n, ty', bi⟩ := e
    intro j bt hlen
    rw [hwrap_cons]
    show annotateBindersOut (m := CheckM) mk d rest (j - 1)
        (mk n (ty'.abstractRange d j) (bt.abstractRange d (j + 1)) bi)
      = wrap rest (j - 1) (mk n ty' (bt.abstract1 (d + j)) bi)
    cases rest with
    | nil =>
      obtain rfl : j = 0 := by simpa using hlen
      rw [hwrap_nil]
      show (pure (mk n (ty'.abstractRange d 0)
          (bt.abstractRange d (0 + 1)) bi) : CheckM Expr)
        = pure (mk n ty' (bt.abstract1 (d + 0)) bi)
      rw [abstractRange_zero, abstractRange_succ, abstractRange_zero]
    | cons e' rest' =>
      have hj1 : 1 ≤ j := by
        simp only [List.length_cons] at hlen
        omega
      have hnode : mk n (ty'.abstractRange d j)
          (bt.abstractRange d (j + 1)) bi
          = (mk n ty' (bt.abstract1 (d + j)) bi).abstractRange
              d ((j - 1) + 1) := by
        have hj : (j - 1) + 1 = j := by omega
        rw [hj, hmkR]
        congr 1
        rw [abstractRange_succ]
      rw [hnode]
      exact ih (j - 1) _ (by
        simp only [List.length_cons] at hlen ⊢
        omega)

/-- Leaf-phase soundness for the annotate ∀-loop. -/
theorem annotatePisLeaf_sound {d : Nat} {t : Expr}
    {k : Nat} {fvs : List Expr} {stk : List AnnotBinderEntryX} {F : Nat}
    {res : Expr}
    (hlen : stk.length = k)
    (hrun : annotatePisLeaf (pureFns mode env F) d t k fvs stk = .ok res) :
    ∃ F', (annotateCore mode env F' (d + k) (t.instantiateList fvs) >>=
      fun leaf' => annotatePisWrap (m := CheckM) d stk (k - 1) leaf')
        = .ok res := by
  unfold annotatePisLeaf at hrun
  obtain ⟨leaf', hleaf, hrun⟩ := bind_okB hrun
  rw [annotate_def] at hleaf
  cases stk with
  | nil =>
    obtain rfl : k = 0 := by simpa using hlen.symm
    unfold annotateBindersOut at hrun
    rw [abstractRange_zero] at hrun
    exact ⟨F, by rw [hleaf, okB_bind]; exact hrun⟩
  | cons e rest =>
    have hk1 : 1 ≤ k := by rw [← hlen]; simp
    have hkeq : (k - 1) + 1 = k := by omega
    refine ⟨F, ?_⟩
    rw [hleaf, okB_bind]
    rw [← annotateBindersOut_wrap (mk := fun n ty b bi => .forallE n ty b ⟨bi⟩)
      (fun n ty b bi d k c => rfl)
      (annotatePisWrap (m := CheckM) d)
      (fun j bt => rfl) (fun n ty' bi rest j bt => rfl)
      (e :: rest) (k - 1) leaf'
      (by simp only [List.length_cons] at hlen ⊢; omega)]
    rw [hkeq]
    exact hrun

/-- A successful annotate-∀-peel run is reproduced by the chained
annotation of the bulk-opened residual followed by the (pure) tails. -/
theorem annotatePis_sound {d : Nat} :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List AnnotBinderEntryX) (F : Nat) (res : Expr),
      stk.length = k →
      annotatePis (pureFns mode env F) d fuel t k fvs stk = .ok res →
      ∃ F', (annotateCore mode env F' (d + k) (t.instantiateList fvs) >>=
        fun leaf' => annotatePisWrap (m := CheckM) d stk (k - 1) leaf')
          = .ok res := by
  intro fuel
  induction fuel with
  | zero =>
    intro t k fvs stk F res hlen hrun
    rw [annotatePis_zero] at hrun
    exact annotatePisLeaf_sound hlen hrun
  | succ fuel ihf =>
    intro t k fvs stk F res hlen hrun
    by_cases hpi : ∃ n ty body mb, t = Expr.forallE n ty body mb
    · obtain ⟨n, ty, body, mb, rfl⟩ := hpi
      rw [annotatePis_succ_pi] at hrun
      obtain ⟨ty', hty', hrun⟩ := bind_okB hrun
      rw [annotate_def] at hty'
      obtain ⟨F', hchain⟩ := ihf body (k + 1) _ _ F res
        (by simpa using hlen) hrun
      obtain ⟨leaf', hleaf, hwrap⟩ := bind_okB hchain
      have hpiL : (Expr.forallE n ty body mb).instantiateList fvs
          = Expr.forallE n (ty.instantiateList fvs)
            (body.instantiateList fvs 1) mb := by
        simp [Expr.instantiateList]
      refine ⟨(max F F') + 1, ?_⟩
      rw [hpiL, annotateCore_forallE_eq]
      rw [annotateCore_mono (Nat.le_max_left F F') hty', okB_bind]
      rw [show (body.instantiateList fvs 1).instantiate1
          (.fvar (d + k) n ty')
          = body.instantiateList (Expr.fvar (d + k) n ty' :: fvs) from
        (Expr.instantiateList_cons ..).symm]
      rw [show d + k + 1 = d + (k + 1) from by omega]
      rw [annotateCore_mono (Nat.le_max_right F F') hleaf, okB_bind,
        pure_bind]
      rw [show (k + 1 : Nat) - 1 = k from rfl] at hwrap
      exact hwrap
    · have ht : ∀ n ty body mb, t ≠ Expr.forallE n ty body mb :=
        fun n ty b mb hh => hpi ⟨n, ty, b, mb, hh⟩
      rw [annotatePis_succ_ne_pi _ ht] at hrun
      exact annotatePisLeaf_sound hlen hrun

/-- Leaf-phase soundness for the annotate λ-loop. -/
theorem annotateLamsLeaf_sound {d : Nat} {t : Expr}
    {k : Nat} {fvs : List Expr} {stk : List AnnotBinderEntryX} {F : Nat}
    {res : Expr}
    (hlen : stk.length = k)
    (hrun : annotateLamsLeaf (pureFns mode env F) d t k fvs stk = .ok res) :
    ∃ F', (annotateCore mode env F' (d + k) (t.instantiateList fvs) >>=
      fun leaf' => annotateLamsWrap (m := CheckM) d stk (k - 1) leaf')
        = .ok res := by
  unfold annotateLamsLeaf at hrun
  obtain ⟨leaf', hleaf, hrun⟩ := bind_okB hrun
  rw [annotate_def] at hleaf
  cases stk with
  | nil =>
    obtain rfl : k = 0 := by simpa using hlen.symm
    unfold annotateBindersOut at hrun
    rw [abstractRange_zero] at hrun
    exact ⟨F, by rw [hleaf, okB_bind]; exact hrun⟩
  | cons e rest =>
    have hk1 : 1 ≤ k := by rw [← hlen]; simp
    have hkeq : (k - 1) + 1 = k := by omega
    refine ⟨F, ?_⟩
    rw [hleaf, okB_bind]
    rw [← annotateBindersOut_wrap (mk := fun n ty b bi => .lam n ty b ⟨bi⟩)
      (fun n ty b bi d k c => rfl)
      (annotateLamsWrap (m := CheckM) d)
      (fun j bt => rfl) (fun n ty' bi rest j bt => rfl)
      (e :: rest) (k - 1) leaf'
      (by simp only [List.length_cons] at hlen ⊢; omega)]
    rw [hkeq]
    exact hrun

/-- A successful annotate-λ-peel run is reproduced by the chained
annotation of the bulk-opened residual followed by the (pure) tails. -/
theorem annotateLams_sound {d : Nat} :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List AnnotBinderEntryX) (F : Nat) (res : Expr),
      stk.length = k →
      annotateLams (pureFns mode env F) d fuel t k fvs stk = .ok res →
      ∃ F', (annotateCore mode env F' (d + k) (t.instantiateList fvs) >>=
        fun leaf' => annotateLamsWrap (m := CheckM) d stk (k - 1) leaf')
          = .ok res := by
  intro fuel
  induction fuel with
  | zero =>
    intro t k fvs stk F res hlen hrun
    rw [annotateLams_zero] at hrun
    exact annotateLamsLeaf_sound hlen hrun
  | succ fuel ihf =>
    intro t k fvs stk F res hlen hrun
    by_cases hlam : ∃ n ty body mb, t = Expr.lam n ty body mb
    · obtain ⟨n, ty, body, mb, rfl⟩ := hlam
      rw [annotateLams_succ_lam] at hrun
      obtain ⟨ty', hty', hrun⟩ := bind_okB hrun
      rw [annotate_def] at hty'
      obtain ⟨F', hchain⟩ := ihf body (k + 1) _ _ F res
        (by simpa using hlen) hrun
      obtain ⟨leaf', hleaf, hwrap⟩ := bind_okB hchain
      have hlamL : (Expr.lam n ty body mb).instantiateList fvs
          = Expr.lam n (ty.instantiateList fvs)
            (body.instantiateList fvs 1) mb := by
        simp [Expr.instantiateList]
      refine ⟨(max F F') + 1, ?_⟩
      rw [hlamL, annotateCore_lam_eq]
      rw [annotateCore_mono (Nat.le_max_left F F') hty', okB_bind]
      rw [show (body.instantiateList fvs 1).instantiate1
          (.fvar (d + k) n ty')
          = body.instantiateList (Expr.fvar (d + k) n ty' :: fvs) from
        (Expr.instantiateList_cons ..).symm]
      rw [show d + k + 1 = d + (k + 1) from by omega]
      rw [annotateCore_mono (Nat.le_max_right F F') hleaf, okB_bind,
        pure_bind]
      rw [show (k + 1 : Nat) - 1 = k from rfl] at hwrap
      exact hwrap
    · have ht : ∀ n ty body mb, t ≠ Expr.lam n ty body mb :=
        fun n ty b mb hh => hlam ⟨n, ty, b, mb, hh⟩
      rw [annotateLams_succ_ne_lam _ ht] at hrun
      exact annotateLamsLeaf_sound hlen hrun

end AnnotSound

end Setlec
