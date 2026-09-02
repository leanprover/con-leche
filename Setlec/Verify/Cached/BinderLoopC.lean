import Setlec.Verify.Cached.DiscC3
import Setlec.Verify.BinderLoop

/-!
# Cached binder-loop walks (task #163, batch 9)

The port of `Setlec/Verify/BinderLoopI.lean`: simulation walks relating
the cached binder-telescope loops (`inferLamsI`/`inferPisI`,
`Setlec/Cached/CoreC.lean`) to the same pure mirrors
(`Setlec/Verify/BinderLoop.lean`) at the fueled record, plus the two
*tail compositions* against `inferBody`'s own λ/∀ tails.  The comparand
side of every statement is byte-identical to the interned original's;
the twin side loses the arena (`SimAt → SimC`, denotation hypotheses →
`RelC`, no `Ext`).

Representation shrinkages, all expected: `IBinderMeta → BinderMeta` and
`NIdx → Name` collapse the stack relations' `denoteBM`/`denoteN` legs
to equations, and `LIdx → Level` collapses `inferPisOutI`'s stack
relation to a pair of equations.

**The peel fuel is not a parameter of these walks.**  Every loop
theorem quantifies over the fuel exactly as the interned original does,
so the clone's constant `peelFuel` and the arena's node count are both
instances, and no proof below reads a property of the fuel value.  The
documented deviation costs nothing here.

**The annotation half is NOT ported — a finding, not a proof wall.**
`Setlec/Cached/CoreC.lean` was cloned (commit `796360e1`) from a `CoreI`
that predates the task #161 P5 write repair (`CoreI`/`BinderLoop`
commits `6ecbc79c`..`03710c8c`, which reached this branch only through
the later `agent/annot-v2` merges), so the cached annotation loops are
an *older program* than the frozen comparand:

1. `annotateBindersOutI`: the clone threads the leaf's `pw?` unchanged
   through the rebuild fold; `annotateBindersOut` (and the interned
   twin) thread `pw?.map fun _ => (annotBinderMeta pw? mb).pw` — the
   datum *just written*.  The two differ above an explicitly annotated
   binder (`pwWritten mb.pw`), i.e. they write different terms.
2. `annotatePisLeafI`: the clone always infers the leaf's sort; the
   comparand's `annotPwPi` first reads a `∀` residual's own datum and
   performs no knot call in that branch.

Both are genuine code-shape differences, so the transposed statements
would be false (1) or unsimulable (2).  The clone must be re-synced
with `CoreI` before `annotateBindersOutC_sim`, `annotatePisLeafC_sim`,
`annotatePisC_sim`, `annotateLamsLeafC_sim`, `annotateLamsC_sim` and
the two annotation tail compositions can be written; the four
`annotPwPiI`/`annotPwLamI`/`annotatePisPwI`/`annotateLamsPwI` walks
have no cached subject at all (the clone has no such helpers).
`RelAStk` below is the prepared stack relation for that resumption.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Setlec.Cached

open Setlec
open Setlec.Cached.ExprC

variable {mode : CheckMode}

variable {env : Env} {f : Nat}

/-- Erasure-only result relation for the loop walks (the port of
`RelD`: the state-free residue of the denotation leg). -/
abbrev RelDC : ExprC → Expr → Prop := RelC

/-- Pushing on the accumulator array conses on its reversed read
(task #97: the loops keep the opened fvars innermost-**last**; the
mirrors' lists stay innermost-first). -/
theorem toListRev_push {α} (a : Array α) (x : α) :
    (a.push x).toList.reverse = x :: a.toList.reverse := by
  simp

theorem toListRev_singleton {α} (x : α) :
    (#[x] : Array α).toList.reverse = [x] := by
  simp

theorem toListRev_empty {α} :
    (#[] : Array α).toList.reverse = ([] : List α) := by
  simp

/-! ## Stack relations -/

/-- Pointwise relation of `inferLamsI` stack entries (the port of
`DenILE`: names and binder metas are trees here, so their legs are
equations). -/
def RelILE : InferLamEntry → InferLamEntryX → Prop
  | (n, tyo, mb), (nx, tyox, mbx) =>
    n = nx ∧ RelC tyo tyox ∧ mb = mbx

def RelILStk : List InferLamEntry → List InferLamEntryX → Prop
  | [], [] => True
  | e :: r, ex :: rx => RelILE e ex ∧ RelILStk r rx
  | _, _ => False

/-- Pointwise relation of annotation-loop stack entries, indexed by
the head entry's binder level (each entry's annotated domain is
well-scoped at its own level, for the out-phase inferences).  Prepared
for the annotation walks, which are blocked on the clone/`CoreI` sync
recorded in the module docstring. -/
def RelAStk (d : Nat) :
    List AnnotBinderEntry → List AnnotBinderEntryX → Nat → Prop
  | [], [], _ => True
  | (n, ty', bi) :: r, (nx, tyx', bix) :: rx, j =>
    (n = nx ∧ bi = bix ∧ RelC ty' tyx' ∧ Expr.WScoped (d + j) tyx') ∧
      RelAStk d r rx (j - 1)
  | _, _, _ => False

/-! ## The infer-λ loop walks -/

theorem inferLamsOutC_sim {d : Nat} :
    ∀ {stk : List InferLamEntry} {stkx : List InferLamEntryX} {j : Nat}
      {cur : ExprC} {curx : Expr} {prevPw : PropWhen} {s₀ : CState},
      CSOK mode env s₀ → RelILStk stk stkx → RelC cur curx →
      SimC mode env s₀ RelDC (inferLamsOutI mode d stk j cur prevPw)
        (inferLamsOut (m := FueledM) mode d stkx j curx prevPw) := by
  intro stk
  induction stk with
  | nil =>
    intro stkx j cur curx prevPw s₀ hs hstk hcur
    cases stkx with
    | nil => exact SimC.pure hs hcur
    | cons ex rx => exact absurd hstk (by simp [RelILStk])
  | cons e rest ihOut =>
    obtain ⟨n, tyo, mb⟩ := e
    intro stkx j cur curx prevPw s₀ hs hstk hcur
    cases stkx with
    | nil => exact absurd hstk (by simp [RelILStk])
    | cons ex rx =>
      obtain ⟨nx, tyox, mbx⟩ := ex
      obtain ⟨⟨hnnm, htyo, hmb⟩, hrest⟩ := hstk
      subst hnnm
      subst hmb
      show SimC mode env s₀ RelDC
        (do
          if mode.verified && !(mb.pw.equiv prevPw) then
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-chain)")
          let tyAbs ← abstractRangeM tyo d j
          let node ← internI (.forallE n tyAbs cur mb)
          inferLamsOutI mode d rest (j - 1) node mb.pw)
        (do
          if mode.verified && !(mb.pw.equiv prevPw) then
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-chain)")
          inferLamsOut (m := FueledM) mode d rx (j - 1)
            (Expr.forallE n (tyox.abstractRange d j) curx mb) mb.pw)
      split
      · exact SimC.throw_bind
      refine SimC.bind_left (abstractRangeM_eff hs htyo)
        (fun s₃ tyAbs hs₃ hQab => ?_)
      refine SimC.bind_left
        (internI_eff hs₃ (n := ExprView.forallE n tyAbs cur mb)
          ⟨hQab.1, hcur.1⟩)
        (fun s₄ node hs₄ hQnode => ?_)
      have hQnode' : RelC node
          (Expr.forallE n (tyox.abstractRange d j) curx mb) := by
        refine ⟨hQnode.1, ?_⟩
        rw [show eraseC node
            = .forallE n (eraseC tyAbs) (eraseC cur) mb from hQnode.2,
          hQab.2, hcur.2]
      exact ihOut hs₄ hrest hQnode'

theorem inferLamsLeafC_sim (ih : SSimC mode env f) {d : Nat}
    {t : ExprC} {tx : Expr} {k : Nat} {fvs : Array ExprC} {ws : List Expr}
    {stk : List InferLamEntry} {stkx : List InferLamEntryX} {s₀ : CState}
    (hs : CSOK mode env s₀) (ht : RelC t tx)
    (hfvs : RelCL fvs.toList.reverse ws) (hstk : RelILStk stk stkx)
    (hw : Expr.WScoped (d + k) (tx.instantiateList ws)) :
    SimC mode env s₀ RelDC
      (inferLamsLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      (inferLamsLeaf mode (fueledFns mode env) d tx k ws stkx) := by
  unfold inferLamsLeafI inferLamsLeaf
  refine SimC.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hQob => ?_)
  refine SimC.bind (ih.infer hs₁ hQob hw)
    (fun s₂ bt btx hs₂ hPbt => ?_)
  obtain ⟨hbtd, hwbt⟩ := hPbt
  -- the λ-chain guard (task #152): the residual's head shape, read on
  -- both sides of the erasure
  refine SimC.view ?_
  obtain ⟨hwc, rfl⟩ := ht
  cases t
  case lam nmN tyN bodyN mbN h bb fb lp =>
    dsimp only [ExprC.view, eraseC]
    refine SimC.bind_left (abstractRangeM_eff hs₂ hbtd)
      (fun s₅ cur hs₅ hQcur => ?_)
    refine SimC.view ?_
    dsimp only [ExprC.view, Expr.lamPw]
    exact inferLamsOutC_sim hs₅ hstk hQcur
  all_goals
    dsimp only [ExprC.view, eraseC, Expr.lamPw]
    by_cases hv : mode.verified = true
    case neg =>
      simp only [if_neg hv]
      refine SimC.bind_left (abstractRangeM_eff hs₂ hbtd)
        (fun s₅ cur hs₅ hQcur => ?_)
      refine SimC.view ?_
      dsimp only [ExprC.view]
      cases hstk0 : stk with
      | nil =>
        cases hstkx0 : stkx with
        | nil =>
          exact inferLamsOutC_sim hs₅ trivial hQcur
        | cons _ _ =>
          rw [hstk0, hstkx0] at hstk
          exact absurd hstk (by simp [RelILStk])
      | cons e0 r0 =>
        cases hstkx0 : stkx with
        | nil =>
          rw [hstk0, hstkx0] at hstk
          exact absurd hstk (by simp [RelILStk])
        | cons e0x r0x =>
          rw [hstk0, hstkx0] at hstk
          obtain ⟨n0, ty0, mb0⟩ := e0
          obtain ⟨n0x, ty0x, mb0x⟩ := e0x
          obtain rfl : mb0x = mb0 := hstk.1.2.2.symm
          dsimp only
          exact inferLamsOutC_sim hs₅ hstk hQcur
    simp only [if_pos hv]
    refine SimC.bind (ih.infer hs₂ hbtd hwbt)
      (fun s₃ btt bttx hs₃ hPbtt => ?_)
    obtain ⟨hbttd, hwbtt⟩ := hPbtt
    refine SimC.bind (ih.whnf hs₃ hbttd hwbtt)
      (fun s₄ wbt wx hs₄ hPw => ?_)
    obtain ⟨hwd, hww⟩ := hPw
    refine SimC.view ?_
    obtain ⟨hwdc, rfl⟩ := hwd
    cases wbt
    case sort v hh bb' fb' lp' =>
      dsimp only [ExprC.view, eraseC]
      -- the leaf validation (task #161): both sides read the same
      -- datum of the same sort; then the fold, per stack head
      cases hstk0 : stk with
      | nil =>
        cases hstkx0 : stkx with
        | nil =>
          dsimp only
          refine SimC.bind_left (abstractRangeM_eff hs₄ hbtd)
            (fun s₅ cur hs₅ hQcur => ?_)
          refine SimC.view ?_
          dsimp only [ExprC.view]
          exact inferLamsOutC_sim hs₅ trivial hQcur
        | cons _ _ =>
          rw [hstk0, hstkx0] at hstk
          exact absurd hstk (by simp [RelILStk])
      | cons e0 r0 =>
        cases hstkx0 : stkx with
        | nil =>
          rw [hstk0, hstkx0] at hstk
          exact absurd hstk (by simp [RelILStk])
        | cons e0x r0x =>
          rw [hstk0, hstkx0] at hstk
          obtain ⟨n0, ty0, mb0⟩ := e0
          obtain ⟨n0x, ty0x, mb0x⟩ := e0x
          obtain rfl : mb0x = mb0 := hstk.1.2.2.symm
          dsimp only
          refine SimC.withStore ?_
          obtain ⟨-, hzeq⟩ := zeronessOfLIGoC_spec (st := default) v
            (memo := {}) PWMemoInvC.empty
            (p := (CStore.zeronessOfLIGo default {} v).1)
            (memo' := (CStore.zeronessOfLIGo default {} v).2) rfl
          rw [hzeq]
          split
          case isFalse => exact SimC.throw_bind
          refine SimC.bind_left (abstractRangeM_eff hs₄ hbtd)
            (fun s₅ cur hs₅ hQcur => ?_)
          refine SimC.view ?_
          dsimp only [ExprC.view]
          exact inferLamsOutC_sim hs₅ hstk hQcur
    all_goals exact SimC.throw

theorem inferLamsC_sim (ih : SSimC mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : ExprC} {tx : Expr} {k : Nat}
      {fvs : Array ExprC} {ws : List Expr}
      {stk : List InferLamEntry} {stkx : List InferLamEntryX}
      {s₀ : CState},
      CSOK mode env s₀ → RelC t tx →
      RelCL fvs.toList.reverse ws → RelILStk stk stkx →
      Expr.WScoped (d + k) (tx.instantiateList ws) →
      SimC mode env s₀ RelDC
        (inferLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel t k fvs stk)
        (inferLams mode (fueledFns mode env) d fuel tx k ws stkx)
  | 0, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    exact inferLamsLeafC_sim ih hs ht hfvs hstk hw
  | fuel + 1, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    show SimC mode env s₀ RelDC
      (do
        match ← viewI t with
        | some (.lam n ty body mb) => do
          let tyo ← instListRevM ty fvs
          let tty ← (coreKnotI mode (mkFEnv env) f).infer (d + k) tyo
          let wtty ← (coreKnotI mode (mkFEnv env) f).whnf (d + k) tty
          match ← viewI wtty with
          | some (.sort _) => do
            let fv ← internI (.fvar (d + k) n tyo)
            inferLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel body (k + 1)
              (fvs.push fv) ((n, tyo, mb) :: stk)
          | _ => throw (.invalid "expected a sort")
        | _ => inferLamsLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      _
    refine SimC.view ?_
    have ht' := ht
    obtain ⟨hwc, rfl⟩ := ht
    cases t
    case lam nm ty body mb h bb fb lp =>
      dsimp only [ExprC.view, eraseC] at hw ⊢
      rw [inferLams_succ_lam]
      obtain ⟨hwty, hwbody, -⟩ := hwc.lam_inv
      have hlamL : (Expr.lam nm (eraseC ty) (eraseC body) mb).instantiateList
          ws = Expr.lam nm ((eraseC ty).instantiateList ws)
            ((eraseC body).instantiateList ws 1) mb := by
        simp [Expr.instantiateList]
      have hwcomp : Expr.WScoped (d + k) ((eraseC ty).instantiateList ws)
          ∧ Expr.WScoped (d + k) ((eraseC body).instantiateList ws 1) := by
        rw [hlamL] at hw
        simpa only [Expr.WScoped] using hw
      refine SimC.bind_left
        (instListRevM_eff (d := 0) hs ⟨hwty, rfl⟩ hfvs)
        (fun s₁ tyo hs₁ hQtyo => ?_)
      refine SimC.bind (ih.infer hs₁ hQtyo hwcomp.1)
        (fun s₂ tty ttyx hs₂ hPtty => ?_)
      obtain ⟨httyd, hwtty⟩ := hPtty
      refine SimC.bind (ih.whnf hs₂ httyd hwtty)
        (fun s₃ wtty wx hs₃ hPw => ?_)
      obtain ⟨hwd, hww⟩ := hPw
      refine SimC.view ?_
      obtain ⟨hwdc, rfl⟩ := hwd
      cases wtty
      case sort u hh bb' fb' lp' =>
        dsimp only [ExprC.view, eraseC]
        refine SimC.bind_left
          (internI_eff hs₃ (n := ExprView.fvar (d + k) nm tyo) hQtyo.1)
          (fun s₄ fv hs₄ hQfv => ?_)
        have hQfv' : RelC fv
            (Expr.fvar (d + k) nm ((eraseC ty).instantiateList ws)) := by
          refine ⟨hQfv.1, ?_⟩
          rw [show eraseC fv = .fvar (d + k) nm (eraseC tyo) from hQfv.2,
            hQtyo.2]
        have hwopen : Expr.WScoped (d + (k + 1))
            ((eraseC body).instantiateList
              (Expr.fvar (d + k) nm ((eraseC ty).instantiateList ws) :: ws)) := by
          rw [Expr.instantiateList_cons]
          have := Expr.WScoped.instantiate1 (n := nm) hwcomp.1 0 hwcomp.2
          simpa [Nat.add_assoc] using this
        refine inferLamsC_sim ih fuel hs₄ ⟨hwbody, rfl⟩
          (by rw [toListRev_push]
              exact RelCL.cons hQfv' hfvs)
          ⟨⟨rfl, hQtyo, rfl⟩, hstk⟩ hwopen
      all_goals exact SimC.throw
    all_goals
      dsimp only [ExprC.view, eraseC]
      rw [inferLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferLamsLeafC_sim ih hs ht' hfvs hstk hw

/-! ## The infer-∀ loop walks (task #100 stage 6: the ∀-rule infers
its codomain sort, so the cached side runs a telescope loop) -/

/-- Pointwise relation of `inferPisI`'s domain-sort stack (levels are
trees here, so both legs are equations — the port of `DenLStk`). -/
def RelLStk : List (Level × PropWhen) → List (Level × PropWhen) → Prop
  | [], [] => True
  | (u, pw) :: r, (ux, pwx) :: rx => (u = ux ∧ pw = pwx) ∧ RelLStk r rx
  | _, _ => False

theorem inferPisOutC_sim :
    ∀ {stk : List (Level × PropWhen)} {stkx : List (Level × PropWhen)}
      {v : Level} {lv : Level} {memo : CStore.PWMemo} {s₀ : CState},
      CSOK mode env s₀ → RelLStk stk stkx → v = lv →
      PWMemoInvC memo →
      SimC mode env s₀ (fun (iv : Level) (ivx : Level) => iv = ivx)
        (inferPisOutI mode stk v memo)
        (inferPisOut (m := FueledM) mode stkx lv) := by
  intro stk
  induction stk with
  | nil =>
    intro stkx v lv memo s₀ hs hstk hv _hminv
    cases stkx with
    | nil => exact SimC.pure hs hv
    | cons ux rx => exact absurd hstk (by simp [RelLStk])
  | cons upw rest ih =>
    obtain ⟨u, pw⟩ := upw
    intro stkx v lv memo s₀ hs hstk hv hminv
    cases stkx with
    | nil => exact absurd hstk (by simp [RelLStk])
    | cons uxp rx =>
      obtain ⟨ux, pwx⟩ := uxp
      obtain ⟨⟨hu, rfl⟩, hrest⟩ := hstk
      subst hu
      subst hv
      show SimC mode env s₀ _
        (do
          let (pv, memo) ← Setlec.Cached.withStore fun st =>
            st.zeronessOfLIGo memo v
          if mode.verified && !(pv.equiv pw) then
            throw (.notImplemented
              "sort-annotation mismatch (forall-cod)")
          internLM (.imax u v) >>= fun v' =>
            inferPisOutI mode rest v' memo)
        (do
          if mode.verified && !((Level.zeronessOf v).equiv pw) then
            throw (.notImplemented
              "sort-annotation mismatch (forall-cod)")
          inferPisOut (m := FueledM) mode rx (.imax u v))
      refine SimC.withStore ?_
      obtain ⟨hminv', hzeq⟩ := zeronessOfLIGoC_spec (st := default) v
        (memo := memo) hminv
        (p := (CStore.zeronessOfLIGo default memo v).1)
        (memo' := (CStore.zeronessOfLIGo default memo v).2) rfl
      dsimp only
      rw [hzeq]
      split
      · exact SimC.throw_bind
      refine SimC.bind_left (internLM_eff hs (.imax u v))
        (fun s₁ v' hs₁ hv' => ?_)
      subst hv'
      exact ih (stkx := rx) (lv := .imax u v) hs₁ hrest rfl hminv'

theorem inferPisLeafC_sim (ih : SSimC mode env f) {d : Nat}
    {t : ExprC} {tx : Expr} {k : Nat} {fvs : Array ExprC} {ws : List Expr}
    {stk : List (Level × PropWhen)} {stkx : List (Level × PropWhen)}
    {s₀ : CState}
    (hs : CSOK mode env s₀) (ht : RelC t tx)
    (hfvs : RelCL fvs.toList.reverse ws) (hstk : RelLStk stk stkx)
    (hw : Expr.WScoped (d + k) (tx.instantiateList ws)) :
    SimC mode env s₀ RelDC
      (inferPisLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      (inferPisLeaf mode (fueledFns mode env) d tx k ws stkx) := by
  unfold inferPisLeafI inferPisLeaf
  refine SimC.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hQob => ?_)
  refine SimC.bind (ih.infer hs₁ hQob hw)
    (fun s₂ bt btx hs₂ hPbt => ?_)
  obtain ⟨hbtd, hwbt⟩ := hPbt
  refine SimC.bind (ih.whnf hs₂ hbtd hwbt)
    (fun s₃ wbt wx hs₃ hPw => ?_)
  obtain ⟨hwd, hww⟩ := hPw
  refine SimC.view ?_
  obtain ⟨hwdc, rfl⟩ := hwd
  cases wbt
  case sort v hh bb fb lp =>
    dsimp only [ExprC.view, eraseC]
    refine SimC.bind (inferPisOutC_sim hs₃ hstk rfl PWMemoInvC.empty)
      (fun s₄ iv ivx hs₄ hiv => ?_)
    exact SimC.of_eff (internI_eff hs₄ (n := ExprView.sort iv) trivial)
      _ (fun s hQ => by
        refine ⟨hQ.1, ?_⟩
        rw [show eraseC s = Expr.sort iv from hQ.2, hiv])
  all_goals exact SimC.throw

theorem inferPisC_sim (ih : SSimC mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : ExprC} {tx : Expr} {k : Nat}
      {fvs : Array ExprC} {ws : List Expr}
      {stk : List (Level × PropWhen)} {stkx : List (Level × PropWhen)}
      {s₀ : CState},
      CSOK mode env s₀ → RelC t tx →
      RelCL fvs.toList.reverse ws → RelLStk stk stkx →
      Expr.WScoped (d + k) (tx.instantiateList ws) →
      SimC mode env s₀ RelDC
        (inferPisI mode (coreKnotI mode (mkFEnv env) f) d fuel t k fvs
          stk)
        (inferPis mode (fueledFns mode env) d fuel tx k ws stkx)
  | 0, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    exact inferPisLeafC_sim ih hs ht hfvs hstk hw
  | fuel + 1, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    show SimC mode env s₀ RelDC
      (do
        match ← viewI t with
        | some (.forallE n ty body mb) => do
          let tyo ← instListRevM ty fvs
          let tty ← (coreKnotI mode (mkFEnv env) f).infer (d + k) tyo
          let wtty ← (coreKnotI mode (mkFEnv env) f).whnf (d + k) tty
          match ← viewI wtty with
          | some (.sort u) => do
            let fv ← internI (.fvar (d + k) n tyo)
            inferPisI mode (coreKnotI mode (mkFEnv env) f) d fuel body
              (k + 1) (fvs.push fv) ((u, mb.pw) :: stk)
          | _ => throw (.invalid "expected a sort")
        | _ =>
          inferPisLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs
            stk)
      _
    refine SimC.view ?_
    have ht' := ht
    obtain ⟨hwc, rfl⟩ := ht
    cases t
    case forallE nm ty body mb h bb fb lp =>
      dsimp only [ExprC.view, eraseC] at hw ⊢
      rw [inferPis_succ_pi]
      obtain ⟨hwty, hwbody, -⟩ := hwc.forallE_inv
      have hpiL : (Expr.forallE nm (eraseC ty) (eraseC body) mb).instantiateList
          ws = Expr.forallE nm ((eraseC ty).instantiateList ws)
            ((eraseC body).instantiateList ws 1) mb := by
        simp [Expr.instantiateList]
      have hwcomp : Expr.WScoped (d + k) ((eraseC ty).instantiateList ws)
          ∧ Expr.WScoped (d + k) ((eraseC body).instantiateList ws 1) := by
        rw [hpiL] at hw
        simpa only [Expr.WScoped] using hw
      refine SimC.bind_left
        (instListRevM_eff (d := 0) hs ⟨hwty, rfl⟩ hfvs)
        (fun s₁ tyo hs₁ hQtyo => ?_)
      refine SimC.bind (ih.infer hs₁ hQtyo hwcomp.1)
        (fun s₂ tty ttyx hs₂ hPtty => ?_)
      obtain ⟨httyd, hwtty⟩ := hPtty
      refine SimC.bind (ih.whnf hs₂ httyd hwtty)
        (fun s₃ wtty wx hs₃ hPw => ?_)
      obtain ⟨hwd, hww⟩ := hPw
      refine SimC.view ?_
      obtain ⟨hwdc, rfl⟩ := hwd
      cases wtty
      case sort u hh bb' fb' lp' =>
        dsimp only [ExprC.view, eraseC]
        refine SimC.bind_left
          (internI_eff hs₃ (n := ExprView.fvar (d + k) nm tyo) hQtyo.1)
          (fun s₄ fv hs₄ hQfv => ?_)
        have hQfv' : RelC fv
            (Expr.fvar (d + k) nm ((eraseC ty).instantiateList ws)) := by
          refine ⟨hQfv.1, ?_⟩
          rw [show eraseC fv = .fvar (d + k) nm (eraseC tyo) from hQfv.2,
            hQtyo.2]
        have hwopen : Expr.WScoped (d + (k + 1))
            ((eraseC body).instantiateList
              (Expr.fvar (d + k) nm ((eraseC ty).instantiateList ws) :: ws)) := by
          rw [Expr.instantiateList_cons]
          have := Expr.WScoped.instantiate1 (n := nm) hwcomp.1 0 hwcomp.2
          simpa [Nat.add_assoc] using this
        exact inferPisC_sim ih fuel hs₄ ⟨hwbody, rfl⟩
          (by rw [toListRev_push]
              exact RelCL.cons hQfv' hfvs)
          ⟨⟨rfl, rfl⟩, hstk⟩ hwopen
      all_goals exact SimC.throw
    all_goals
      dsimp only [ExprC.view, eraseC]
      rw [inferPis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferPisLeafC_sim ih hs ht' hfvs hstk hw

/-! ## Tail compositions: the infer loops against the chained bodies'
own tails, with the result scoping recovered from the chained run

The two `*_atF` normalizations below are pure comparand-side lemmas
(no cached state occurs in them); they are byte-identical copies of
`BinderLoopI`'s private originals, restated here because the cached
tier does not import the interned walks. -/

private theorem inferLamTail_atF {env : Env} (d : Nat) (nm : Name)
    (tyx bodyx : Expr) (mbx : BinderMeta) (F : Nat) :
    ((do
      let bt ← (fueledFns mode env).infer (d + 1)
        (bodyx.instantiate1 (.fvar d nm tyx))
      if mode.verified then
        match bodyx.lamPw with
        | some pwI =>
          unless mbx.pw.equiv pwI do
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-chain)")
        | none => do
          let btt ← (fueledFns mode env).infer (d + 1) bt
          let vb ← ensureSort (fueledFns mode env) env (d + 1) btt
          unless (Level.zeronessOf vb).equiv mbx.pw do
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-leaf)")
      pure (Expr.forallE nm tyx (bt.abstract1 d) mbx)) : FueledM Expr).val F
    = (inferTypeCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d nm tyx))
        >>= fun bt => (do
          if mode.verified then
            match bodyx.lamPw with
            | some pwI =>
              unless mbx.pw.equiv pwI do
                throw (.notImplemented
                  "sort-annotation mismatch (lam-cod-chain)")
            | none => do
              let btt ← inferTypeCore mode env F (d + 1) bt
              let vb ← ensureSortCore mode env F (d + 1) btt
              unless (Level.zeronessOf vb).equiv mbx.pw do
                throw (.notImplemented
                  "sort-annotation mismatch (lam-cod-leaf)")
          pure (Expr.forallE nm tyx (bt.abstract1 d) mbx))) := by
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  by_cases hv : mode.verified = true
  case neg => rw [if_neg hv, if_neg hv]; rfl
  rw [if_pos hv, if_pos hv]
  cases hbp : bodyx.lamPw with
  | some pwI =>
    dsimp only
    by_cases hc : mbx.pw.equiv pwI = true
    · rw [if_pos hc, if_pos hc]; rfl
    · rw [if_neg hc, if_neg hc]; rfl
  | none =>
    dsimp only
    rw [FueledM.atF_bind]
    congr 1
    funext btt
    rw [FueledM.atF_bind, ensureSort_atF]
    congr 1
    funext vb
    by_cases hc : (Level.zeronessOf vb).equiv mbx.pw = true
    · rw [if_pos hc, if_pos hc]; rfl
    · rw [if_neg hc, if_neg hc]; rfl

/-- The λ-inference loop against `inferBody`'s own λ-tail (task #100
stage 6: the tail is a pure rebuild — the λ-annotation re-check died
with the stored annotations). -/
theorem inferLamsC_tail_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d fuel : Nat} {b t fv : ExprC} {bodyx tyx : Expr} {nm : Name}
    {mbbi : BinderInfo} {mbpw : PropWhen} {s₀ : CState}
    (hs : CSOK mode env s₀)
    (hbody : RelC b bodyx)
    (hty : RelC t tyx)
    (hfv : RelC fv (.fvar d nm tyx))
    (hwty : Expr.WScoped d tyx) (hwbody : Expr.WScoped d bodyx) :
    SimC mode env s₀ (RelEC d)
      (inferLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, t, ⟨mbbi, mbpw⟩)])
      (do
        let bt ← (fueledFns mode env).infer (d + 1)
          (bodyx.instantiate1 (.fvar d nm tyx))
        if mode.verified then
          match bodyx.lamPw with
          | some pwI =>
            unless (⟨mbbi, mbpw⟩ : BinderMeta).pw.equiv pwI do
              throw (.notImplemented
                "sort-annotation mismatch (lam-cod-chain)")
          | none => do
            let btt ← (fueledFns mode env).infer (d + 1) bt
            let vb ← ensureSort (fueledFns mode env) env (d + 1) btt
            unless (Level.zeronessOf vb).equiv
                (⟨mbbi, mbpw⟩ : BinderMeta).pw do
              throw (.notImplemented
                "sort-annotation mismatch (lam-cod-leaf)")
        pure (Expr.forallE nm tyx (bt.abstract1 d) ⟨mbbi, mbpw⟩)) := by
  have hwopen : Expr.WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nm tyx]) := by
    rw [instList_single]
    exact Expr.WScoped.instantiate1 hwty 0 hwbody
  have hcore : SimC mode env s₀ RelDC
      (inferLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, t, ⟨mbbi, mbpw⟩)])
      (inferLams mode (fueledFns mode env) d fuel bodyx 1 [Expr.fvar d nm tyx]
        [(nm, tyx, ⟨mbbi, mbpw⟩)]) := by
    refine inferLamsC_sim ih fuel hs hbody
      (by rw [toListRev_singleton]; exact RelCL.cons hfv RelCL.nil)
      ⟨⟨rfl, hty, rfl⟩, trivial⟩ hwopen
  refine SimC.wp (SimC.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [inferLams_atF] at hF
    obtain ⟨F', hchain⟩ := inferLams_sound fuel bodyx 1
      [Expr.fvar d nm tyx] [(nm, tyx, ⟨mbbi, mbpw⟩)] F res rfl
      (by
        intro x hx
        rcases List.mem_singleton.mp hx with rfl
        exact ⟨_, _, _, rfl⟩)
      hF
    refine ⟨F', ?_⟩
    rw [inferLamTail_atF]
    obtain ⟨bt, hbt, htail⟩ := bind_okB hchain
    have hbt' : inferTypeCore mode env F' (d + 1)
        (bodyx.instantiate1 (.fvar d nm tyx)) = .ok bt := by
      rw [← instList_single bodyx (Expr.fvar d nm tyx)]
      exact hbt
    rw [hbt', okB_bind]
    unfold inferLamsTail at htail
    revert htail
    cases hbp : bodyx.lamPw with
    | some pwI =>
      intro htail
      have hbl : bodyx.isLam = true := by
        cases bodyx <;> first | rfl | exact nomatch hbp
      simp only [hbl, Bool.not_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte] at htail
      unfold inferLamsWrap at htail
      dsimp only
      by_cases hg : (mode.verified
          && !((⟨mbbi, mbpw⟩ : BinderMeta).pw.equiv pwI)) = true
      · rw [if_pos hg] at htail
        exact nomatch htail
      rw [if_neg hg] at htail
      by_cases hv : mode.verified = true
      · rw [if_pos hv]
        have hpw : (⟨mbbi, mbpw⟩ : BinderMeta).pw.equiv pwI = true := by
          by_cases hc : (⟨mbbi, mbpw⟩ : BinderMeta).pw.equiv pwI = true
          · exact hc
          · exact absurd (by simp [hv, hc]) hg
        rw [if_pos hpw]
        exact htail
      · rw [if_neg hv]
        exact htail
    | none =>
      intro htail
      have hbl : bodyx.isLam = false := by
        cases bodyx <;> first | rfl | exact nomatch hbp
      simp only [hbl, Bool.not_false, Bool.and_true] at htail
      dsimp only
      by_cases hv : mode.verified = true
      case neg =>
        rw [if_neg hv] at htail ⊢
        unfold inferLamsWrap at htail
        rw [if_neg (by simp [hv])] at htail
        exact htail
      rw [if_pos hv] at htail ⊢
      rw [infer_def] at htail
      obtain ⟨btt, hbtt, htail⟩ := bind_okB htail
      rw [hbtt, okB_bind]
      rw [ensureSort_def] at htail
      obtain ⟨v, hvv, htail⟩ := bind_okB htail
      rw [hvv, okB_bind]
      try dsimp only at htail ⊢
      by_cases hz : (Level.zeronessOf v).equiv
          (⟨mbbi, mbpw⟩ : BinderMeta).pw = true
      case neg =>
        rw [if_neg hz] at htail
        exact nomatch htail
      rw [if_pos hz] at htail
      rw [if_pos hz]
      unfold inferLamsWrap at htail
      rw [if_neg (by simp [PropWhen.equiv_refl])] at htail
      exact htail
  case hsc =>
    intro v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [inferLamTail_atF] at hF
    obtain ⟨bt, hbt, hF⟩ := bind_okB hF
    have hwbt : Expr.WScoped (d + 1) bt :=
      inferTypeCore_WScoped henv F hbt
        (Expr.WScoped.instantiate1 hwty 0 hwbody)
    have hres : vv = Expr.forallE nm tyx (bt.abstract1 d) ⟨mbbi, mbpw⟩ := by
      revert hF
      by_cases hv : mode.verified = true
      case neg =>
        rw [if_neg hv]
        intro hF
        injection hF with hres
        exact hres.symm
      rw [if_pos hv]
      cases bodyx.lamPw with
      | some pwI =>
        dsimp only
        by_cases hc : (⟨mbbi, mbpw⟩ : BinderMeta).pw.equiv pwI = true
        · rw [if_pos hc]
          intro hF
          injection hF with hres
          exact hres.symm
        · rw [if_neg hc]
          intro hF
          exact nomatch hF
      | none =>
        dsimp only
        intro hF
        obtain ⟨btt, -, hF⟩ := bind_okB hF
        obtain ⟨v, -, hF⟩ := bind_okB hF
        revert hF
        by_cases hc : (Level.zeronessOf v).equiv
            (⟨mbbi, mbpw⟩ : BinderMeta).pw = true
        · rw [if_pos hc]
          intro hF
          injection hF with hres
          exact hres.symm
        · rw [if_neg hc]
          intro hF
          exact nomatch hF
    subst hres
    exact (by
      simp only [Expr.WScoped]
      exact ⟨hwty, Setlec.WScoped.abstract1 0 hwbt⟩ :
      Expr.WScoped d (Expr.forallE nm tyx (bt.abstract1 d) ⟨mbbi, mbpw⟩))

private theorem inferPiTail_atF {env : Env} (d : Nat) (nm : Name)
    (tyx bodyx : Expr) (lu : Level) (pw : PropWhen) (F : Nat) :
    ((do
      let v ← ensureSort (fueledFns mode env) env (d + 1)
        (← (fueledFns mode env).infer (d + 1)
          (bodyx.instantiate1 (.fvar d nm tyx)))
      if mode.verified then
        unless (Level.zeronessOf v).equiv pw do
          throw (.notImplemented "sort-annotation mismatch (forall-cod)")
      pure (Expr.sort (.imax lu v))) : FueledM Expr).val F
    = (inferTypeCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d nm tyx))
        >>= fun bt => ensureSortCore mode env F (d + 1) bt >>= fun v =>
        (do
          if mode.verified then
            unless (Level.zeronessOf v).equiv pw do
              throw (.notImplemented
                "sort-annotation mismatch (forall-cod)")
          pure (Expr.sort (.imax lu v)))) := by
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  rw [FueledM.atF_bind, ensureSort_atF]
  congr 1
  funext v
  by_cases hv : mode.verified = true
  case neg => rw [if_neg hv, if_neg hv]; rfl
  rw [if_pos hv, if_pos hv]
  by_cases hz : (Level.zeronessOf v).equiv pw = true
  · rw [if_pos hz, if_pos hz]; rfl
  · rw [if_neg hz, if_neg hz]; rfl

/-- The ∀-inference loop against `inferBody`'s own ∀-tail (task #100
stage 6: the codomain sort is inferred, not read off an annotation). -/
theorem inferPisC_tail_sim (ih : SSimC mode env f)
    {d fuel : Nat} {b fv : ExprC} {bodyx tyx : Expr}
    {nmx : Name} {u : Level} {lu : Level} {pw : PropWhen} {s₀ : CState}
    (hs : CSOK mode env s₀)
    (hbody : RelC b bodyx)
    (hlu : u = lu)
    (hfv : RelC fv (.fvar d nmx tyx))
    (hwty : Expr.WScoped d tyx) (hwbody : Expr.WScoped d bodyx) :
    SimC mode env s₀ (RelEC d)
      (inferPisI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(u, pw)])
      (do
        let v ← ensureSort (fueledFns mode env) env (d + 1)
          (← (fueledFns mode env).infer (d + 1)
            (bodyx.instantiate1 (.fvar d nmx tyx)))
        if mode.verified then
          unless (Level.zeronessOf v).equiv pw do
            throw (.notImplemented
              "sort-annotation mismatch (forall-cod)")
        pure (Expr.sort (.imax lu v))) := by
  have hwopen : Expr.WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nmx tyx]) := by
    rw [instList_single]
    exact Expr.WScoped.instantiate1 hwty 0 hwbody
  have hcore : SimC mode env s₀ RelDC
      (inferPisI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(u, pw)])
      (inferPis mode (fueledFns mode env) d fuel bodyx 1
        [Expr.fvar d nmx tyx] [(lu, pw)]) := by
    refine inferPisC_sim ih fuel hs hbody
      (by rw [toListRev_singleton]; exact RelCL.cons hfv RelCL.nil)
      ⟨⟨hlu, rfl⟩, trivial⟩ hwopen
  refine SimC.wp (SimC.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [inferPis_atF] at hF
    obtain ⟨F', hchain⟩ := inferPis_sound fuel bodyx 1
      [Expr.fvar d nmx tyx] [(lu, pw)] F res rfl (Nat.le_refl 1) hF
    refine ⟨F', ?_⟩
    rw [inferPiTail_atF]
    obtain ⟨bt, hbt, hwrap⟩ := bind_okB hchain
    have hbt' : inferTypeCore mode env F' (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx)) = .ok bt := by
      rw [← instList_single bodyx (Expr.fvar d nmx tyx)]
      exact hbt
    rw [hbt', okB_bind]
    unfold inferPisWrap at hwrap
    obtain ⟨v, hv, hwrap⟩ := bind_okB hwrap
    rw [ensureSort_def] at hv
    have hv' : ensureSortCore mode env F' (d + 1) bt = .ok v := hv
    rw [hv', okB_bind]
    dsimp only at hwrap ⊢
    by_cases hver : mode.verified = true
    case neg =>
      rw [if_neg hver] at hwrap ⊢
      unfold inferPisWrap at hwrap
      exact hwrap
    rw [if_pos hver] at hwrap ⊢
    by_cases hz : (Level.zeronessOf v).equiv pw = true
    case neg =>
      rw [if_neg hz] at hwrap
      exact nomatch hwrap
    rw [if_pos hz] at hwrap ⊢
    unfold inferPisWrap at hwrap
    exact hwrap
  case hsc =>
    intro v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [inferPiTail_atF] at hF
    obtain ⟨bt, hbt, hF⟩ := bind_okB hF
    obtain ⟨v, hv, hF⟩ := bind_okB hF
    revert hF
    by_cases hver : mode.verified = true
    case neg =>
      rw [if_neg hver]
      intro hF
      injection hF with hres
      subst hres
      simp [Expr.WScoped]
    rw [if_pos hver]
    by_cases hz : (Level.zeronessOf v).equiv pw = true
    · rw [if_pos hz]
      intro hF
      injection hF with hres
      subst hres
      simp [Expr.WScoped]
    · rw [if_neg hz]
      intro hF
      exact nomatch hF

end Setlec.Cached
