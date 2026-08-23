import Setlec.Verify.BetaSpine
import Setlec.Verify.Abstract
import Setlec.Verify.AbstractRange
import Setlec.Verify.InferLeaves
import Setlec.Verify.Leaves

/-!
# Binder-telescope loops and their identification with the chained
bodies (task #72)

The interned twins' binder cases (`annotatePisI`/`annotateLamsI`/
`inferLamsI`, `Setlec/Kernel/CoreI.lean`) peel a whole binder telescope
in one loop — bulk-opening with an fvar accumulator, substituting only
each binder's domain on the way in, and rebuilding with one
`abstractRange` per domain and one over the leaf.  This file provides
the pure mirrors (generic over the core record, like `BetaSpine`'s) and
proves the **soundness of each loop against the chained spec**: a
successful mirror run at the pure fueled knot is reproduced by the
original one-binder-at-a-time body at some fuel
(`inferLams_sound_body`, `annotatePis_sound_body`,
`annotateLams_sound_body`).  The interned walks
(`Setlec/Verify/DiscI4.lean`, `DiscI6.lean`) compose their simulation
against the mirrors with these theorems, so the `Expr`-level
specification — and everything above it — is unchanged.

Key steps:

* the *wraps* (`inferLamsWrap`, …) — the chained bodies' post-recursion
  tails, folded over the peeled binders innermost-first;
* the out-phase/wrap identification: the loop's rebuild with
  `abstractRange` equals the nested `abstract1` chain
  (`abstractRange_succ`), the chained tails' re-inferences of the
  freshly built binder nodes are value-determined by the peel phase's
  domain facts (with `inferTypeCore_depth_inv` where the tail runs one
  binder deeper), and — for the λ-annotation re-checks — the chained
  `infer` re-opens exactly the body it just closed
  (`abstract1_instantiate1` with the leaf toolkit);
* the peel induction — direct (head-first), gluing with fuel
  monotonicity; the peel fuel is semantically transparent (its leaf
  phase is exactly the chained spec's next step, whatever the residual
  head is).
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Setlec

open Expr

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## The pure mirrors -/

/-- Mirror stack entry of `inferLamsI`: binder name, opened domain,
binder meta, the λ-annotation, the domain's sort. -/
abbrev InferLamEntryX := Name × Expr × BinderMeta × Level × Level

/-- Mirror stack entry of the annotation loops: binder name, annotated
opened domain, binder info. -/
abbrev AnnotBinderEntryX := Name × Expr × BinderInfo

/-- Pure mirror of `inferLamsOutI`. -/
def inferLamsOut (d : Nat) :
    List InferLamEntryX → Nat → Level → Expr → m Expr
  | [], _j, _vcur, cur => pure cur
  | (n, tyo, mb, v, u) :: rest, j, vcur, cur => do
    unless ← liftFueled "level comparison" (Level.isEquiv v vcur) do
      throw (.invalid "λ-annotation does not match the body's sort")
    let node := Expr.forallE n (tyo.abstractRange d j) cur mb
    match rest with
    | [] => pure node
    | e' :: rest' => inferLamsOut d (e' :: rest') (j - 1) (.imax u v) node

/-- Pure mirror of `inferLamsLeafI`. -/
def inferLamsLeaf (r : CoreFns m) (d : Nat) (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List InferLamEntryX) : m Expr := do
  let bt ← r.infer (d + k) (t.instantiateList fvs)
  let tbt ← r.infer (d + k) bt
  match ← r.whnf (d + k) tbt with
  | .sort v' => inferLamsOut d stk (k - 1) v' (bt.abstractRange d k)
  | _ => throw (.invalid "expected a sort")

/-- Pure mirror of `inferLamsI`. -/
def inferLams (r : CoreFns m) (d : Nat) :
    Nat → Expr → Nat → List Expr → List InferLamEntryX → m Expr
  | fuel + 1, t, k, fvs, stk =>
    match t with
    | .lam n ty body mb =>
      match mb.cod with
      | some v => do
        let tyo := ty.instantiateList fvs
        let tty ← r.infer (d + k) tyo
        match ← r.whnf (d + k) tty with
        | .sort u =>
          inferLams r d fuel body (k + 1) (Expr.fvar (d + k) n tyo :: fvs)
            ((n, tyo, mb, v, u) :: stk)
        | _ => throw (.invalid "expected a sort")
      | none => throw (.internal "unannotated λ-binder reached inferType")
    | t => inferLamsLeaf r d t k fvs stk
  | 0, t, k, fvs, stk => inferLamsLeaf r d t k fvs stk

/-- Pure mirror of `annotatePisOutI`. -/
def annotatePisOut (r : CoreFns m) (d : Nat) :
    List AnnotBinderEntryX → Nat → Level → Expr → m Expr
  | [], _j, _vcur, cur => pure cur
  | (n, ty', bi) :: rest, j, vcur, cur =>
    let node := Expr.forallE n (ty'.abstractRange d j) cur ⟨bi, some vcur⟩
    match rest with
    | [] => pure node
    | e' :: rest' => do
      let tty ← r.infer (d + j) ty'
      match ← r.whnf (d + j) tty with
      | .sort u => annotatePisOut r d (e' :: rest') (j - 1) (.imax u vcur) node
      | _ => throw (.invalid "expected a sort")

/-- Pure mirror of `annotatePisLeafI`. -/
def annotatePisLeaf (r : CoreFns m) (env : Env) (d : Nat) (t : Expr)
    (k : Nat) (fvs : List Expr) (stk : List AnnotBinderEntryX) : m Expr := do
  let leaf' ← r.annotate (d + k) (t.instantiateList fvs)
  let tb ← r.infer (d + k) leaf'
  let v ← ensureSort r env (d + k) tb
  annotatePisOut r d stk (k - 1) v (leaf'.abstractRange d k)

/-- Pure mirror of `annotatePisI`. -/
def annotatePis (r : CoreFns m) (env : Env) (d : Nat) :
    Nat → Expr → Nat → List Expr → List AnnotBinderEntryX → m Expr
  | fuel + 1, t, k, fvs, stk =>
    match t with
    | .forallE n ty body mb => do
      let ty' ← r.annotate (d + k) (ty.instantiateList fvs)
      annotatePis r env d fuel body (k + 1)
        (Expr.fvar (d + k) n ty' :: fvs) ((n, ty', mb.bi) :: stk)
    | t => annotatePisLeaf r env d t k fvs stk
  | 0, t, k, fvs, stk => annotatePisLeaf r env d t k fvs stk

/-- Pure mirror of `annotateLamsOutI`. -/
def annotateLamsOut (r : CoreFns m) (d : Nat) :
    List AnnotBinderEntryX → Nat → Level → Expr → m Expr
  | [], _j, _vcur, cur => pure cur
  | (n, ty', bi) :: rest, j, vcur, cur =>
    let node := Expr.lam n (ty'.abstractRange d j) cur ⟨bi, some vcur⟩
    match rest with
    | [] => pure node
    | e' :: rest' => do
      let tty ← r.infer (d + j) ty'
      match ← r.whnf (d + j) tty with
      | .sort u => do
        unless ← liftFueled "level comparison" (Level.isEquiv vcur vcur) do
          throw (.invalid "λ-annotation does not match the body's sort")
        annotateLamsOut r d (e' :: rest') (j - 1) (.imax u vcur) node
      | _ => throw (.invalid "expected a sort")

/-- Pure mirror of `annotateLamsLeafI`. -/
def annotateLamsLeaf (r : CoreFns m) (env : Env) (d : Nat) (t : Expr)
    (k : Nat) (fvs : List Expr) (stk : List AnnotBinderEntryX) : m Expr := do
  let leaf' ← r.annotate (d + k) (t.instantiateList fvs)
  let bt ← r.infer (d + k) leaf'
  let tbt ← r.infer (d + k) bt
  let v ← ensureSort r env (d + k) tbt
  annotateLamsOut r d stk (k - 1) v (leaf'.abstractRange d k)

/-- Pure mirror of `annotateLamsI`. -/
def annotateLams (r : CoreFns m) (env : Env) (d : Nat) :
    Nat → Expr → Nat → List Expr → List AnnotBinderEntryX → m Expr
  | fuel + 1, t, k, fvs, stk =>
    match t with
    | .lam n ty body mb => do
      let ty' ← r.annotate (d + k) (ty.instantiateList fvs)
      annotateLams r env d fuel body (k + 1)
        (Expr.fvar (d + k) n ty' :: fvs) ((n, ty', mb.bi) :: stk)
    | t => annotateLamsLeaf r env d t k fvs stk
  | 0, t, k, fvs, stk => annotateLamsLeaf r env d t k fvs stk

/-! ## The chained tails (wraps) -/

/-- The chained `inferBody` λ-tail folded over the peeled binders
(innermost first, `j` the head entry's binder level). -/
def inferLamsWrap (r : CoreFns m) (d : Nat) :
    List InferLamEntryX → Nat → Expr → m Expr
  | [], _j, bt => pure bt
  | (n, tyo, mb, v, _u) :: rest, j, bt => do
    let tbt ← r.infer (d + j + 1) bt
    match ← r.whnf (d + j + 1) tbt with
    | .sort v' => do
      unless ← liftFueled "level comparison" (Level.isEquiv v v') do
        throw (.invalid "λ-annotation does not match the body's sort")
      inferLamsWrap r d rest (j - 1)
        (.forallE n tyo (bt.abstract1 (d + j)) mb)
    | _ => throw (.invalid "expected a sort")

/-- The chained `annotateBody` ∀-tail folded over the peeled
binders. -/
def annotatePisWrap (r : CoreFns m) (env : Env) (d : Nat) :
    List AnnotBinderEntryX → Nat → Expr → m Expr
  | [], _j, body' => pure body'
  | (n, ty', bi) :: rest, j, body' => do
    let tb ← r.infer (d + j + 1) body'
    let v ← ensureSort r env (d + j + 1) tb
    annotatePisWrap r env d rest (j - 1)
      (.forallE n ty' (body'.abstract1 (d + j)) ⟨bi, some v⟩)

/-- The chained `annotateBody` λ-tail folded over the peeled
binders. -/
def annotateLamsWrap (r : CoreFns m) (env : Env) (d : Nat) :
    List AnnotBinderEntryX → Nat → Expr → m Expr
  | [], _j, body' => pure body'
  | (n, ty', bi) :: rest, j, body' => do
    let bt ← r.infer (d + j + 1) body'
    let tbt ← r.infer (d + j + 1) bt
    let v ← ensureSort r env (d + j + 1) tbt
    annotateLamsWrap r env d rest (j - 1)
      (.lam n ty' (body'.abstract1 (d + j)) ⟨bi, some v⟩)

/-! ## Unfolding equations -/

section Unfold

variable {r : CoreFns m} {env : Env} {d : Nat}

theorem inferLams_zero (t : Expr) (k : Nat) (fvs : List Expr)
    (stk : List InferLamEntryX) :
    inferLams r d 0 t k fvs stk = inferLamsLeaf r d t k fvs stk := rfl

theorem inferLams_succ_lam (fuel : Nat) (n : Name) (ty body : Expr)
    (bi : BinderInfo) (v : Level) (k : Nat) (fvs : List Expr)
    (stk : List InferLamEntryX) :
    inferLams r d (fuel + 1) (.lam n ty body ⟨bi, some v⟩) k fvs stk
      = (do
        let tty ← r.infer (d + k) (ty.instantiateList fvs)
        match ← r.whnf (d + k) tty with
        | .sort u =>
          inferLams r d fuel body (k + 1)
            (Expr.fvar (d + k) n (ty.instantiateList fvs) :: fvs)
            ((n, ty.instantiateList fvs, ⟨bi, some v⟩, v, u) :: stk)
        | _ => throw (.invalid "expected a sort")) := rfl

theorem inferLams_succ_lam_none (fuel : Nat) (n : Name) (ty body : Expr)
    (bi : BinderInfo) (k : Nat) (fvs : List Expr)
    (stk : List InferLamEntryX) :
    inferLams r d (fuel + 1) (.lam n ty body ⟨bi, none⟩) k fvs stk
      = throw (.internal "unannotated λ-binder reached inferType") := rfl

theorem inferLams_succ_ne_lam (fuel : Nat) {t : Expr}
    (ht : ∀ n ty body mb, t ≠ .lam n ty body mb) (k : Nat)
    (fvs : List Expr) (stk : List InferLamEntryX) :
    inferLams r d (fuel + 1) t k fvs stk
      = inferLamsLeaf r d t k fvs stk := by
  cases t with
  | lam n ty body mb => exact absurd rfl (ht n ty body mb)
  | _ => rw [inferLams] <;> exact fun _ _ _ _ h => nomatch h

theorem inferLamsOut_cons (n : Name) (tyo : Expr) (mb : BinderMeta)
    (v u : Level) (e' : InferLamEntryX) (rest : List InferLamEntryX)
    (j : Nat) (vcur : Level) (cur : Expr) :
    inferLamsOut (m := m) d ((n, tyo, mb, v, u) :: e' :: rest) j vcur cur
      = (do
        unless ← liftFueled "level comparison" (Level.isEquiv v vcur) do
          throw (.invalid "λ-annotation does not match the body's sort")
        inferLamsOut d (e' :: rest) (j - 1) (.imax u v)
          (Expr.forallE n (tyo.abstractRange d j) cur mb)) := rfl

theorem inferLamsOut_single (n : Name) (tyo : Expr) (mb : BinderMeta)
    (v u : Level) (j : Nat) (vcur : Level) (cur : Expr) :
    inferLamsOut (m := m) d [(n, tyo, mb, v, u)] j vcur cur
      = (do
        unless ← liftFueled "level comparison" (Level.isEquiv v vcur) do
          throw (.invalid "λ-annotation does not match the body's sort")
        pure (Expr.forallE n (tyo.abstractRange d j) cur mb)) := rfl

/-! Shape equations of the fueled bodies on binder nodes (definitional;
the fuel steps once). -/

theorem inferTypeCore_forallE_eq (env : Env) (F d : Nat) (n : Name)
    (ty body : Expr) (bi : BinderInfo) (v : Level) :
    inferTypeCore env (F + 1) d (.forallE n ty body ⟨bi, some v⟩)
      = (inferTypeCore env F d ty >>= fun tty =>
         whnf env F d tty >>= fun w =>
         match w with
         | .sort u => pure (Expr.sort (.imax u v))
         | _ => throw (.invalid "expected a sort")) := rfl

theorem inferTypeCore_forallE_eq' (env : Env) (F d : Nat) (n : Name)
    (ty body : Expr) (mb : BinderMeta) (v : Level)
    (hcod : mb.cod = some v) :
    inferTypeCore env (F + 1) d (.forallE n ty body mb)
      = (inferTypeCore env F d ty >>= fun tty =>
         whnf env F d tty >>= fun w =>
         match w with
         | .sort u => pure (Expr.sort (.imax u v))
         | _ => throw (.invalid "expected a sort")) := by
  obtain ⟨bi, cod⟩ := mb
  obtain rfl : cod = some v := hcod
  exact inferTypeCore_forallE_eq env F d n ty body bi v

theorem inferTypeCore_lam_eq (env : Env) (F d : Nat) (n : Name)
    (ty body : Expr) (bi : BinderInfo) (v : Level) :
    inferTypeCore env (F + 1) d (.lam n ty body ⟨bi, some v⟩)
      = (inferTypeCore env F d ty >>= fun tty =>
         whnf env F d tty >>= fun w =>
         match w with
         | .sort _ => do
           let bt ← inferTypeCore env F (d + 1)
             (body.instantiate1 (.fvar d n ty))
           let tbt ← inferTypeCore env F (d + 1) bt
           let w' ← whnf env F (d + 1) tbt
           match w' with
           | .sort v' => do
             unless ← liftFueled "level comparison" (Level.isEquiv v v') do
               throw (.invalid "λ-annotation does not match the body's sort")
             pure (Expr.forallE n ty (bt.abstract1 d) ⟨bi, some v⟩)
           | _ => throw (.invalid "expected a sort")
         | _ => throw (.invalid "expected a sort")) := rfl

theorem annotateCore_forallE_eq (env : Env) (F d : Nat) (n : Name)
    (ty body : Expr) (mb : BinderMeta) :
    annotateCore env (F + 1) d (.forallE n ty body mb)
      = (annotateCore env F d ty >>= fun ty' =>
         annotateCore env F (d + 1) (body.instantiate1 (.fvar d n ty')) >>=
         fun body' => inferTypeCore env F (d + 1) body' >>= fun tb =>
         ensureSortCore env F (d + 1) tb >>= fun v =>
         pure (Expr.forallE n ty' (body'.abstract1 d) ⟨mb.bi, some v⟩)) := rfl

theorem annotateCore_lam_eq (env : Env) (F d : Nat) (n : Name)
    (ty body : Expr) (mb : BinderMeta) :
    annotateCore env (F + 1) d (.lam n ty body mb)
      = (annotateCore env F d ty >>= fun ty' =>
         annotateCore env F (d + 1) (body.instantiate1 (.fvar d n ty')) >>=
         fun body' => inferTypeCore env F (d + 1) body' >>= fun bt =>
         inferTypeCore env F (d + 1) bt >>= fun tbt =>
         ensureSortCore env F (d + 1) tbt >>= fun v =>
         pure (Expr.lam n ty' (body'.abstract1 d) ⟨mb.bi, some v⟩)) := rfl

theorem ensureSortCore_eq (env : Env) (F d : Nat) (e : Expr) :
    ensureSortCore env F d e
      = (whnf env F d e >>= fun w =>
         match w with
         | .sort u => pure u
         | _ => throw (.invalid "expected a sort")) := rfl

/-- `whnf` is the identity on sorts (two fuel steps in). -/
theorem whnf_sort (env : Env) (F d : Nat) (u : Level) :
    whnf env (F + 2) d (.sort u) = .ok (.sort u) := rfl

end Unfold

private theorem bind_okB {α β : Type} {x : Except CheckError α}
    {f : α → Except CheckError β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => rw [hx] at h; exact nomatch h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

private theorem okB_bind {α β : Type} (a : α)
    (f : α → Except CheckError β) :
    ((Except.ok a : Except CheckError α) >>= f) = f a := rfl

/-! ## `atF` equations and fuel monotonicity -/

section AtF

variable {env : Env}

theorem inferLamsOut_atF (d : Nat) :
    ∀ (stk : List InferLamEntryX) (j : Nat) (vcur : Level) (cur : Expr)
      (F : Nat),
      (inferLamsOut (m := FueledM) d stk j vcur cur).val F
        = inferLamsOut (m := CheckM) d stk j vcur cur
  | [], _, _, _, _ => rfl
  | (n, tyo, mb, v, u) :: rest, j, vcur, cur, F => by
    cases rest with
    | nil =>
      rw [inferLamsOut_single, inferLamsOut_single]
      rw [FueledM.atF_bind, liftFueled_atF]
      cases Level.isEquiv v vcur with
      | none => rfl
      | some b => cases b <;> rfl
    | cons e' rest' =>
      rw [inferLamsOut_cons, inferLamsOut_cons]
      rw [FueledM.atF_bind, liftFueled_atF]
      cases Level.isEquiv v vcur with
      | none => rfl
      | some b =>
        cases b with
        | true =>
          simp only [↓reduceIte]
          exact inferLamsOut_atF d (e' :: rest') (j - 1) _ _ F
        | false => rfl

theorem inferLamsLeaf_atF (d : Nat) (t : Expr) (k : Nat)
    (fvs : List Expr) (stk : List InferLamEntryX) (F : Nat) :
    (inferLamsLeaf (fueledFns env) d t k fvs stk).val F
      = inferLamsLeaf (pureFns env F) d t k fvs stk := by
  unfold inferLamsLeaf
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  rw [FueledM.atF_bind]
  congr 1
  funext tbt
  rw [FueledM.atF_bind]
  congr 1
  funext w
  cases w <;> first
    | rfl
    | exact inferLamsOut_atF d stk (k - 1) _ _ F

theorem inferLams_atF (d : Nat) :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List InferLamEntryX) (F : Nat),
      (inferLams (fueledFns env) d fuel t k fvs stk).val F
        = inferLams (pureFns env F) d fuel t k fvs stk
  | 0, t, k, fvs, stk, F => inferLamsLeaf_atF d t k fvs stk F
  | fuel + 1, t, k, fvs, stk, F => by
    by_cases hlam : ∃ n ty body mb, t = Expr.lam n ty body mb
    · obtain ⟨n, ty, body, ⟨bi, cod⟩, rfl⟩ := hlam
      cases cod with
      | none => rw [inferLams_succ_lam_none, inferLams_succ_lam_none]; rfl
      | some v =>
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

theorem inferLamsWrap_mono {d : Nat} :
    ∀ {stk : List InferLamEntryX} {j : Nat} {bt : Expr} {F F' : Nat},
      F ≤ F' → ∀ {res : Expr},
      inferLamsWrap (pureFns env F) d stk j bt = .ok res →
      inferLamsWrap (pureFns env F') d stk j bt = .ok res := by
  intro stk
  induction stk with
  | nil => intro j bt F F' hle res h; exact h
  | cons e rest ih =>
    obtain ⟨n, tyo, mb, v, u⟩ := e
    intro j bt F F' hle res h
    unfold inferLamsWrap at h ⊢
    obtain ⟨tbt, htbt, h⟩ := bind_okB h
    rw [infer_def] at htbt
    rw [infer_def, inferTypeCore_mono hle htbt, okB_bind]
    obtain ⟨w, hw, h⟩ := bind_okB h
    rw [whnf_def] at hw
    rw [whnf_def, whnf_mono hle hw, okB_bind]
    cases w <;> try exact h
    dsimp only at h ⊢
    obtain ⟨b, hb, h⟩ := bind_okB h
    rw [hb, okB_bind]
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact nomatch h
    | true =>
      simp only [↓reduceIte] at h ⊢
      try dsimp only at h ⊢
      exact ih hle h

end AtF

/-! ## Out-phase/wrap identification and peel soundness (infer) -/

section InferSound

variable {env : Env}

/-- Peel-phase facts for an `inferLams` stack entry at binder level
`j`. -/
def ILEntryOK (env : Env) (d j : Nat) : InferLamEntryX → Prop
  | (_n, tyo, mb, v, u) =>
    mb.cod = some v ∧ WScoped (d + j) tyo ∧
    ∃ F tty, inferTypeCore env F (d + j) tyo = .ok tty ∧
      whnf env F (d + j) tty = .ok (.sort u)

/-- The stack invariant: entry facts at descending binder levels. -/
def ILStkOK (env : Env) (d : Nat) : List InferLamEntryX → Nat → Prop
  | [], _ => True
  | e :: rest, j => ILEntryOK env d j e ∧ ILStkOK env d rest (j - 1)

/-- A successful out-phase run is reproduced by the chained tails at
some fuel, given the body-type facts. -/
theorem inferLamsOut_wrap {d : Nat} :
    ∀ (stk : List InferLamEntryX) (j : Nat) (vcur : Level) (bt : Expr)
      (res : Expr),
      stk.length = j + 1 →
      ILStkOK env d stk j →
      WScoped (d + j + 1) bt →
      (∃ F₀ tbt, inferTypeCore env F₀ (d + j + 1) bt = .ok tbt ∧
        whnf env F₀ (d + j + 1) tbt = .ok (.sort vcur)) →
      inferLamsOut (m := CheckM) d stk j vcur (bt.abstractRange d (j + 1))
          = .ok res →
      ∃ F', inferLamsWrap (pureFns env F') d stk j bt = .ok res := by
  intro stk
  induction stk with
  | nil => intro j vcur bt res hlen; exact nomatch hlen
  | cons e rest ih =>
    obtain ⟨n, tyo, mb, v, u⟩ := e
    intro j vcur bt res hlen hok hwbt hfacts hrun
    obtain ⟨⟨hcod, hwtyo, Fty, tty, htty, hwtty⟩, hokRest⟩ := hok
    obtain ⟨F₀, tbt, htbt, hwhnf⟩ := hfacts
    cases rest with
    | nil =>
      obtain rfl : j = 0 := by simpa using hlen
      rw [inferLamsOut_single] at hrun
      obtain ⟨b, hb, hrun⟩ := bind_okB hrun
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hrun
        exact nomatch hrun
      | true =>
        simp only [↓reduceIte] at hrun
        try dsimp only at hrun
        injection hrun with hres
        refine ⟨F₀, ?_⟩
        unfold inferLamsWrap
        rw [infer_def, htbt, okB_bind]
        rw [whnf_def, hwhnf, okB_bind]
        dsimp only
        rw [hb, okB_bind]
        simp only [↓reduceIte]
        try dsimp only
        have h1 : tyo.abstractRange d 0 = tyo := abstractRange_zero ..
        have h2 : bt.abstractRange d (0 + 1) 0
            = bt.abstract1 (d + 0) 0 := by
          rw [abstractRange_succ, abstractRange_zero]
        rw [h1, h2] at hres
        show Except.ok (Expr.forallE n tyo (bt.abstract1 (d + 0) 0) mb)
          = Except.ok res
        rw [hres]
    | cons e' rest' =>
      have hj1 : 1 ≤ j := by
        simp only [List.length_cons] at hlen
        omega
      rw [inferLamsOut_cons] at hrun
      obtain ⟨b, hb, hrun⟩ := bind_okB hrun
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hrun
        exact nomatch hrun
      | true =>
        simp only [↓reduceIte] at hrun
        try dsimp only at hrun
        have hjeq : d + (j - 1) + 1 = d + j := by omega
        have hnode : Expr.forallE n (tyo.abstractRange d j)
            (bt.abstractRange d (j + 1)) mb
            = (Expr.forallE n tyo (bt.abstract1 (d + j)) mb).abstractRange
                d ((j - 1) + 1) := by
          have hj : (j - 1) + 1 = j := by omega
          rw [hj]
          show _ = Expr.forallE n (tyo.abstractRange d j 0)
            ((bt.abstract1 (d + j) 0).abstractRange d j 1) mb
          rw [abstractRange_succ]
        have hwnode : WScoped (d + (j - 1) + 1)
            (Expr.forallE n tyo (bt.abstract1 (d + j)) mb) := by
          rw [hjeq]
          have habs : WScoped (d + j) (bt.abstract1 (d + j)) :=
            WScoped.abstract1 0 hwbt
          exact (by simp only [WScoped]; exact ⟨hwtyo, habs⟩ :
            WScoped (d + j) (Expr.forallE n tyo (bt.abstract1 (d + j)) mb))
        have hfacts' : ∃ F₁ tbt', inferTypeCore env F₁ (d + (j - 1) + 1)
              (Expr.forallE n tyo (bt.abstract1 (d + j)) mb) = .ok tbt' ∧
            whnf env F₁ (d + (j - 1) + 1) tbt'
              = .ok (.sort (.imax u v)) := by
          refine ⟨(Fty + 2) + 1, .sort (.imax u v), ?_, ?_⟩
          · rw [hjeq]
            rw [inferTypeCore_forallE_eq' env (Fty + 2) (d + j) n tyo
              (bt.abstract1 (d + j)) mb v hcod]
            rw [inferTypeCore_mono (by omega : Fty ≤ Fty + 2) htty, okB_bind]
            rw [whnf_mono (by omega : Fty ≤ Fty + 2) hwtty, okB_bind]
            rfl
          · rw [hjeq]
            exact whnf_sort env (Fty + 1) (d + j) (.imax u v)
        rw [hnode] at hrun
        obtain ⟨F', hwrap'⟩ := ih (j - 1) (.imax u v)
          (Expr.forallE n tyo (bt.abstract1 (d + j)) mb) res
          (by simp only [List.length_cons] at hlen ⊢; omega)
          hokRest hwnode hfacts' hrun
        refine ⟨max F' F₀, ?_⟩
        unfold inferLamsWrap
        rw [infer_def,
          inferTypeCore_mono (Nat.le_max_right F' F₀) htbt, okB_bind]
        rw [whnf_def,
          whnf_mono (Nat.le_max_right F' F₀) hwhnf, okB_bind]
        dsimp only
        rw [hb, okB_bind]
        simp only [↓reduceIte]
        try dsimp only
        exact inferLamsWrap_mono (Nat.le_max_left F' F₀) hwrap'


/-- Leaf-phase soundness: the mirror's leaf run is the chained
inference of the bulk-opened residual followed by the tails. -/
theorem inferLamsLeaf_sound (henv : EnvWF env) {d : Nat} {t : Expr}
    {k : Nat} {fvs : List Expr} {stk : List InferLamEntryX} {F : Nat}
    {res : Expr}
    (hlen : stk.length = k)
    (hok : ILStkOK env d stk (k - 1))
    (hw : WScoped (d + k) (t.instantiateList fvs))
    (hrun : inferLamsLeaf (pureFns env F) d t k fvs stk = .ok res) :
    ∃ F', (inferTypeCore env F' (d + k) (t.instantiateList fvs) >>=
      fun bt => inferLamsWrap (pureFns env F') d stk (k - 1) bt)
        = .ok res := by
  unfold inferLamsLeaf at hrun
  obtain ⟨bt, hbt, hrun⟩ := bind_okB hrun
  rw [infer_def] at hbt
  obtain ⟨tbt, htbt, hrun⟩ := bind_okB hrun
  rw [infer_def] at htbt
  obtain ⟨w, hww, hrun⟩ := bind_okB hrun
  rw [whnf_def] at hww
  obtain ⟨v', rfl⟩ : ∃ v', w = Expr.sort v' := by
    cases w with
    | sort v'' => exact ⟨v'', rfl⟩
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
  cases stk with
  | nil =>
    obtain rfl : k = 0 := by simpa using hlen.symm
    unfold inferLamsOut at hrun
    rw [abstractRange_zero] at hrun
    injection hrun with hres
    refine ⟨F, ?_⟩
    rw [hbt, okB_bind]
    unfold inferLamsWrap
    rw [hres]
    rfl
  | cons e rest =>
    have hk1 : 1 ≤ k := by
      rw [← hlen]
      simp
    have hkeq : (k - 1) + 1 = k := by omega
    have hwbt : WScoped (d + (k - 1) + 1) bt := by
      rw [show d + (k - 1) + 1 = d + k from by omega]
      exact inferTypeCore_WScoped henv F hbt hw
    have hfacts : ∃ F₀ tbt', inferTypeCore env F₀ (d + (k - 1) + 1) bt
          = .ok tbt' ∧
        whnf env F₀ (d + (k - 1) + 1) tbt' = .ok (.sort v') := by
      refine ⟨F, tbt, ?_, ?_⟩ <;>
        rw [show d + (k - 1) + 1 = d + k from by omega]
      · exact htbt
      · exact hww
    have hrun' : inferLamsOut (m := CheckM) d (e :: rest) (k - 1) v'
        (bt.abstractRange d ((k - 1) + 1)) = .ok res := by
      rw [hkeq]
      exact hrun
    obtain ⟨F', hwrap⟩ := inferLamsOut_wrap (e :: rest) (k - 1) v' bt res
      (by simp only [List.length_cons] at hlen ⊢; omega)
      hok hwbt hfacts hrun'
    refine ⟨max F F', ?_⟩
    rw [inferTypeCore_mono (Nat.le_max_left F F') hbt, okB_bind]
    exact inferLamsWrap_mono (Nat.le_max_right F F') hwrap



/-- A successful peel run is reproduced by the chained inference of the
bulk-opened residual followed by the chained tails, at some fuel. -/
theorem inferLams_sound (henv : EnvWF env) {d : Nat} :
    ∀ (fuel : Nat) (t : Expr) (k : Nat) (fvs : List Expr)
      (stk : List InferLamEntryX) (F : Nat) (res : Expr),
      stk.length = k →
      ILStkOK env d stk (k - 1) →
      WScoped (d + k) (t.instantiateList fvs) →
      inferLams (pureFns env F) d fuel t k fvs stk = .ok res →
      ∃ F', (inferTypeCore env F' (d + k) (t.instantiateList fvs) >>=
        fun bt => inferLamsWrap (pureFns env F') d stk (k - 1) bt)
          = .ok res := by
  intro fuel
  induction fuel with
  | zero =>
    intro t k fvs stk F res hlen hok hw hrun
    rw [inferLams_zero] at hrun
    exact inferLamsLeaf_sound henv hlen hok hw hrun
  | succ fuel ihf =>
    intro t k fvs stk F res hlen hok hw hrun
    by_cases hlam : ∃ n ty body mb, t = Expr.lam n ty body mb
    · obtain ⟨n, ty, body, ⟨bi, cod⟩, rfl⟩ := hlam
      cases cod with
      | none =>
        rw [inferLams_succ_lam_none] at hrun
        exact nomatch hrun
      | some v =>
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
        -- the opened lam node's components
        have hlamL : (Expr.lam n ty body ⟨bi, some v⟩).instantiateList fvs
            = Expr.lam n (ty.instantiateList fvs)
              (body.instantiateList fvs 1) ⟨bi, some v⟩ := by
          simp [Expr.instantiateList]
        have hwcomp : WScoped (d + k) (ty.instantiateList fvs)
            ∧ WScoped (d + k) (body.instantiateList fvs 1) := by
          rw [hlamL] at hw
          simpa only [WScoped] using hw
        have hwopen : WScoped (d + (k + 1))
            ((body.instantiateList fvs 1).instantiate1
              (.fvar (d + k) n (ty.instantiateList fvs))) := by
          have := WScoped.instantiate1 (n := n) hwcomp.1 0 hwcomp.2
          simpa [Nat.add_assoc] using this
        have hwopen' : WScoped (d + (k + 1))
            (body.instantiateList
              (Expr.fvar (d + k) n (ty.instantiateList fvs) :: fvs)) := by
          rw [Expr.instantiateList_cons]
          exact hwopen
        have hstk' : ILStkOK env d
            ((n, ty.instantiateList fvs, ⟨bi, some v⟩, v, u) :: stk)
            ((k + 1) - 1) := by
          show ILEntryOK env d k (n, ty.instantiateList fvs,
            ⟨bi, some v⟩, v, u) ∧ ILStkOK env d stk (k - 1)
          refine ⟨⟨rfl, hwcomp.1, F, tty, htty, hww⟩, hok⟩
        obtain ⟨F', hchain⟩ := ihf body (k + 1) _ _ F res
          (by simpa using hlen) hstk' hwopen' hrun
        -- reassemble the chained lam inference
        obtain ⟨bt, hbt, hwrap⟩ := bind_okB hchain
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
        rw [inferTypeCore_mono (Nat.le_max_right F F') hbt, okB_bind]
        -- the wrap's head step is the lam tail
        have hwrap' := inferLamsWrap_mono (F' := max F F')
          (Nat.le_max_right F F') hwrap
        rw [show (k + 1 : Nat) - 1 = k from rfl] at hwrap'
        unfold inferLamsWrap at hwrap'
        obtain ⟨tbt, htbt, hwrap'⟩ := bind_okB hwrap'
        rw [infer_def] at htbt
        rw [show d + k + 1 = d + (k + 1) from by omega] at htbt
        rw [htbt, okB_bind]
        obtain ⟨w', hw', hwrap'⟩ := bind_okB hwrap'
        rw [whnf_def] at hw'
        rw [show d + k + 1 = d + (k + 1) from by omega] at hw'
        rw [hw', okB_bind]
        obtain ⟨v', rfl⟩ : ∃ v', w' = Expr.sort v' := by
          cases w' with
          | sort v'' => exact ⟨v'', rfl⟩
          | bvar i => exact nomatch hwrap'
          | fvar idx nm tt => exact nomatch hwrap'
          | const nm us => exact nomatch hwrap'
          | app f a => exact nomatch hwrap'
          | lam nm tt b mm => exact nomatch hwrap'
          | forallE nm tt b mm => exact nomatch hwrap'
          | letE nm tt vv b => exact nomatch hwrap'
          | lit l => exact nomatch hwrap'
          | proj sp i e => exact nomatch hwrap'
        dsimp only at hwrap' ⊢
        obtain ⟨b, hb, hwrap'⟩ := bind_okB hwrap'
        rw [hb, okB_bind]
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hwrap'
          exact nomatch hwrap'
        | true =>
          simp only [↓reduceIte] at hwrap' ⊢
          try dsimp only at hwrap' ⊢
          exact inferLamsWrap_mono (Nat.le_succ (max F F')) hwrap'
    · have ht : ∀ n ty body mb, t ≠ Expr.lam n ty body mb :=
        fun n ty b mb hh => hlam ⟨n, ty, b, mb, hh⟩
      rw [inferLams_succ_ne_lam _ ht] at hrun
      exact inferLamsLeaf_sound henv hlen hok hw hrun

end InferSound

end Setlec
