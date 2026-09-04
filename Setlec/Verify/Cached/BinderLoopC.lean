import Setlec.Verify.Cached.DiscC3
import Setlec.Verify.BinderLoop

/-!
# Cached binder-loop walks (task #163, batches 9 + 11)

The port of `Setlec/Verify/BinderLoopI.lean`: simulation walks relating
the cached binder-telescope loops (`inferLamsI`/`inferPisI`,
`annotatePisI`/`annotateLamsI`, `Setlec/Cached/CoreC.lean`) to the same
pure mirrors (`Setlec/Verify/BinderLoop.lean`) at the fueled record,
plus the four *tail compositions* against `inferBody`'s and
`annotateBody`'s own λ/∀ tails.  The comparand side of every statement
is byte-identical to the interned original's; the twin side loses the
arena (`SimAt → SimC`, denotation hypotheses → `RelC`, no `Ext`).

Representation shrinkages, all expected: `IBinderMeta → BinderMeta` and
`NIdx → Name` collapse the stack relations' `denoteBM`/`denoteN` legs
to equations, and `LIdx → Level` collapses `inferPisOutI`'s stack
relation to a pair of equations.

**The peel fuel is not a parameter of these walks.**  Every loop
theorem quantifies over the fuel exactly as the interned original does,
so the clone's constant `peelFuel` and the arena's node count are both
instances, and no proof below reads a property of the fuel value.  The
documented deviation costs nothing here.

**The annotation half (batch 11).**  It had been blocked: the clone
(commit `796360e1`) predated the task #161 P5 write repair, so its
`annotateBindersOutI` threaded the leaf's `pw?` unchanged and its
`annotatePisLeafI` always inferred the leaf's sort — an *older
program* than the frozen comparand, for which the transposed statements
would have been false, resp. unsimulable.  Batch 10 re-synced the
clone's annotation block with `CoreI` clause by clause (the CoreI/CoreC
diff over that block is now the type renames only), and batch 11 ports
the walks: `annotateBindersOutC_sim`, `annotPwPiC_sim`/`annotPwLamC_sim`,
`annotatePisPwC_sim`/`annotateLamsPwC_sim`, the two leaf walks, the two
fuelled loops and the two annotation tail compositions.  Two further
collapses show up only here:

* `denoteBM_annotBinderMeta` becomes the definitional
  `annotBinderMetaI_eq` (the clone's meta *is* the spec's).
* `simAt_withStore_pure` becomes `SimC.pure`: the cached `withStore` is
  `fun rd => pure (rd default)`.  It is kept under the name
  `simC_withStore_pure` so the two `annotPw*` walks read like their
  originals.

The `mk`/`mkX` premise of `annotateBindersOutC_sim` is the transposition
of the interned `denoteNode`-agreement premise: `WFcV` of the built view
plus `ofViewE ∘ eraseCV` agreement (what `internI_eff` consumes and
produces here).

With this the port of `BinderLoopI.lean` is COMPLETE — every theorem of
the interned module has its cached twin below, in source order.
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
well-scoped at its own level, for the out-phase inferences) — the port
of `DenAStk`. -/
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
        rw [show node
            = .forallE n tyAbs cur mb from hQnode.2,
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
  case lam nmN tyN bodyN mbN =>
    dsimp only [ExprC.view]
    refine SimC.bind_left (abstractRangeM_eff hs₂ hbtd)
      (fun s₅ cur hs₅ hQcur => ?_)
    refine SimC.view ?_
    dsimp only [ExprC.view, Expr.lamPw]
    exact inferLamsOutC_sim hs₅ hstk hQcur
  all_goals
    dsimp only [ExprC.view, Expr.lamPw]
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
    case sort v =>
      dsimp only [ExprC.view]
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
    case lam nm ty body mb =>
      dsimp only [ExprC.view] at hw ⊢
      rw [inferLams_succ_lam]
      obtain ⟨hwty, hwbody, -⟩ := hwc.lam_inv
      have hlamL : (Expr.lam nm ty body mb).instantiateList
          ws = Expr.lam nm ((Expr.instantiateList ty ws))
            ((Expr.instantiateList body ws 1)) mb := by
        simp [Expr.instantiateList]
      have hwcomp : Expr.WScoped (d + k) ((Expr.instantiateList ty ws))
          ∧ Expr.WScoped (d + k) ((Expr.instantiateList body ws 1)) := by
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
      case sort u =>
        dsimp only [ExprC.view]
        refine SimC.bind_left
          (internI_eff hs₃ (n := ExprView.fvar (d + k) nm tyo) hQtyo.1)
          (fun s₄ fv hs₄ hQfv => ?_)
        have hQfv' : RelC fv
            (Expr.fvar (d + k) nm ((Expr.instantiateList ty ws))) := by
          refine ⟨hQfv.1, ?_⟩
          rw [show fv = .fvar (d + k) nm tyo from hQfv.2,
            hQtyo.2]
        have hwopen : Expr.WScoped (d + (k + 1))
            ((Expr.instantiateList body
              (Expr.fvar (d + k) nm (ty.instantiateList ws) :: ws))) := by
          rw [Expr.instantiateList_cons]
          have := Expr.WScoped.instantiate1 (n := nm) hwcomp.1 0 hwcomp.2
          simpa [Nat.add_assoc] using this
        refine inferLamsC_sim ih fuel hs₄ ⟨hwbody, rfl⟩
          (by rw [toListRev_push]
              exact RelCL.cons hQfv' hfvs)
          ⟨⟨rfl, hQtyo, rfl⟩, hstk⟩ hwopen
      all_goals exact SimC.throw
    all_goals
      dsimp only [ExprC.view]
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
  case sort v =>
    dsimp only [ExprC.view]
    refine SimC.bind (inferPisOutC_sim hs₃ hstk rfl PWMemoInvC.empty)
      (fun s₄ iv ivx hs₄ hiv => ?_)
    exact SimC.of_eff (internI_eff hs₄ (n := ExprView.sort iv) trivial)
      _ (fun s hQ => by
        refine ⟨hQ.1, ?_⟩
        rw [show s = Expr.sort iv from hQ.2, hiv])
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
    case forallE nm ty body mb =>
      dsimp only [ExprC.view] at hw ⊢
      rw [inferPis_succ_pi]
      obtain ⟨hwty, hwbody, -⟩ := hwc.forallE_inv
      have hpiL : (Expr.forallE nm ty body mb).instantiateList
          ws = Expr.forallE nm ((Expr.instantiateList ty ws))
            ((Expr.instantiateList body ws 1)) mb := by
        simp [Expr.instantiateList]
      have hwcomp : Expr.WScoped (d + k) ((Expr.instantiateList ty ws))
          ∧ Expr.WScoped (d + k) ((Expr.instantiateList body ws 1)) := by
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
      case sort u =>
        dsimp only [ExprC.view]
        refine SimC.bind_left
          (internI_eff hs₃ (n := ExprView.fvar (d + k) nm tyo) hQtyo.1)
          (fun s₄ fv hs₄ hQfv => ?_)
        have hQfv' : RelC fv
            (Expr.fvar (d + k) nm ((Expr.instantiateList ty ws))) := by
          refine ⟨hQfv.1, ?_⟩
          rw [show fv = .fvar (d + k) nm tyo from hQfv.2,
            hQtyo.2]
        have hwopen : Expr.WScoped (d + (k + 1))
            ((Expr.instantiateList body
              (Expr.fvar (d + k) nm (ty.instantiateList ws) :: ws))) := by
          rw [Expr.instantiateList_cons]
          have := Expr.WScoped.instantiate1 (n := nm) hwcomp.1 0 hwcomp.2
          simpa [Nat.add_assoc] using this
        exact inferPisC_sim ih fuel hs₄ ⟨hwbody, rfl⟩
          (by rw [toListRev_push]
              exact RelCL.cons hQfv' hfvs)
          ⟨⟨rfl, rfl⟩, hstk⟩ hwopen
      all_goals exact SimC.throw
    all_goals
      dsimp only [ExprC.view]
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

/-! ## The ∀-annotation loop walks -/

/-- The clone's `annotBinderMetaI` *is* the spec's `annotBinderMeta`
(`IBinderMeta = BinderMeta` here, so the interned walk's
`denoteBM_annotBinderMeta` transport collapses to this equation). -/
theorem annotBinderMetaI_eq (pw? : Option PropWhen) (mb : BinderMeta) :
    annotBinderMetaI pw? mb = annotBinderMeta pw? mb := by
  cases pw? <;> rfl

theorem annotateBindersOutC_sim
    {mk : Name → ExprC → ExprC → BinderMeta → ExprView ExprC}
    {mkX : Name → Expr → Expr → BinderMeta → Expr}
    (hmk : ∀ (n : Name) (ty : ExprC) (tyx : Expr) (b : ExprC) (bx : Expr)
      (mi : BinderMeta), RelC ty tyx → RelC b bx →
      WFcV (mk n ty b mi) ∧
        ofViewE (eraseCV (mk n ty b mi)) = mkX n tyx bx mi) {d : Nat} :
    ∀ {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {j : Nat} {pw? : Option PropWhen} {cur : ExprC} {curx : Expr}
      {s₀ : CState},
      CSOK mode env s₀ → RelAStk d stk stkx j → RelC cur curx →
      SimC mode env s₀ RelDC (annotateBindersOutI mk d pw? stk j cur)
        (annotateBindersOut (m := FueledM) mkX d pw? stkx j curx) := by
  intro stk
  induction stk with
  | nil =>
    intro stkx j pw? cur curx s₀ hs hstk hcur
    cases stkx with
    | nil => exact SimC.pure hs hcur
    | cons ex rx => exact absurd hstk (by simp [RelAStk])
  | cons e rest ihOut =>
    obtain ⟨n, ty', bi⟩ := e
    intro stkx j pw? cur curx s₀ hs hstk hcur
    cases stkx with
    | nil => exact absurd hstk (by simp [RelAStk])
    | cons ex rx =>
      obtain ⟨nx, tyx', bix⟩ := ex
      obtain ⟨⟨hnnm, hbmr, hty', hwty'⟩, hrest⟩ := hstk
      subst hnnm
      subst hbmr
      show SimC mode env s₀ RelDC
        (do
          let tyAbs ← abstractRangeM ty' d j
          let node ← internI (mk n tyAbs cur (annotBinderMetaI pw? bi))
          annotateBindersOutI mk d
            (pw?.map fun _ => (annotBinderMetaI pw? bi).pw)
            rest (j - 1) node)
        (annotateBindersOut (m := FueledM) mkX d
          (pw?.map fun _ => (annotBinderMeta pw? bi).pw) rx (j - 1)
          (mkX n (tyx'.abstractRange d j) curx (annotBinderMeta pw? bi)))
      -- task #161 P5: both folds thread the datum just written; the
      -- clone's meta rewrite is definitional here
      simp only [annotBinderMetaI_eq]
      refine SimC.bind_left (abstractRangeM_eff hs hty')
        (fun s₁ tyAbs hs₁ hQab => ?_)
      refine SimC.bind_left
        (internI_eff hs₁
          (hmk n tyAbs (tyx'.abstractRange d j) cur curx
            (annotBinderMeta pw? bi) hQab hcur).1)
        (fun s₂ node hs₂ hQnode => ?_)
      refine ihOut hs₂ hrest ⟨hQnode.1, ?_⟩
      rw [hQnode.2,
        (hmk n tyAbs (tyx'.abstractRange d j) cur curx
          (annotBinderMeta pw? bi) hQab hcur).2]

/-- A bare store read against a pure fueled result (the write's last
step: `zeronessOfLIGo` on the sort level).  The cached `withStore` is
`pure ∘ (· default)`, so the interned `simAt_withStore_pure` collapses
to `SimC.pure`. -/
private theorem simC_withStore_pure {β α : Type}
    {P : β → α → Prop} {rd : CStore → β} {a : α} {s₀ : CState}
    (hs : CSOK mode env s₀) (h : P (rd default) a) :
    SimC mode env s₀ P (Setlec.Cached.withStore rd) (pure a) :=
  SimC.pure hs h

/-- **The telescope datum's walk (task #161 P5).**  Both sides read the
annotated body's head first — a ∀ body hands on its own datum (the
chain rule) — and only otherwise pay the one inference the telescope's
collapse needs. -/
theorem annotPwPiC_sim (ih : SSimC mode env f) {d : Nat}
    {body' : ExprC} {body'x : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hl : RelC body' body'x)
    (hw : Expr.WScoped d body'x) :
    SimC mode env s₀ (fun (v : PropWhen) (vx : PropWhen) => v = vx)
      (annotPwPiI (coreKnotI mode (mkFEnv env) f) d body')
      (annotPwPi (fueledFns mode env) env d body'x) := by
  unfold annotPwPiI annotPwPi
  refine SimC.view ?_
  have hl' := hl
  obtain ⟨hwc, rfl⟩ := hl
  cases body'
  case forallE nmN tyN bodyN mbN =>
    dsimp only [ExprC.view, Expr.forallPw]
    exact SimC.pure hs rfl
  all_goals
    dsimp only [ExprC.view, Expr.forallPw]
    refine SimC.bind (ih.infer hs hl' hw)
      (fun s₂ bt btx hs₂ hPbt => ?_)
    obtain ⟨hbtd, hwbt⟩ := hPbt
    refine SimC.bind (ensureSortC_sim ih hs₂ hbtd hwbt)
      (fun s₃ v lv hs₃ hPv => ?_)
    obtain rfl : v = lv := hPv
    obtain ⟨-, hzeq⟩ := zeronessOfLIGoC_spec (st := default) v
      (memo := {}) PWMemoInvC.empty
      (p := (CStore.zeronessOfLIGo default {} v).1)
      (memo' := (CStore.zeronessOfLIGo default {} v).2) rfl
    exact simC_withStore_pure hs₃ hzeq

/-- The λ twin of `annotPwPiC_sim`. -/
theorem annotPwLamC_sim (ih : SSimC mode env f) {d : Nat}
    {body' : ExprC} {body'x : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hl : RelC body' body'x)
    (hw : Expr.WScoped d body'x) :
    SimC mode env s₀ (fun (v : PropWhen) (vx : PropWhen) => v = vx)
      (annotPwLamI (coreKnotI mode (mkFEnv env) f) d body')
      (annotPwLam (fueledFns mode env) env d body'x) := by
  unfold annotPwLamI annotPwLam
  refine SimC.view ?_
  have hl' := hl
  obtain ⟨hwc, rfl⟩ := hl
  cases body'
  case lam nmN tyN bodyN mbN =>
    dsimp only [ExprC.view, Expr.lamPw]
    exact SimC.pure hs rfl
  all_goals
    dsimp only [ExprC.view, Expr.lamPw]
    refine SimC.bind (ih.infer hs hl' hw)
      (fun s₂ bt btx hs₂ hPbt => ?_)
    obtain ⟨hbtd, hwbt⟩ := hPbt
    refine SimC.bind (ih.infer hs₂ hbtd hwbt)
      (fun s₃ btt bttx hs₃ hPbtt => ?_)
    obtain ⟨hbttd, hwbtt⟩ := hPbtt
    refine SimC.bind (ensureSortC_sim ih hs₃ hbttd hwbtt)
      (fun s₄ vb lvb hs₄ hPv => ?_)
    obtain rfl : vb = lvb := hPv
    obtain ⟨-, hzeq⟩ := zeronessOfLIGoC_spec (st := default) vb
      (memo := {}) PWMemoInvC.empty
      (p := (CStore.zeronessOfLIGo default {} vb).1)
      (memo' := (CStore.zeronessOfLIGo default {} vb).2) rfl
    exact simC_withStore_pure hs₄ hzeq

/-- The gated forms the telescope loops use. -/
theorem annotatePisPwC_sim (ih : SSimC mode env f) {d k : Nat}
    {leaf' : ExprC} {leafx : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hl : RelC leaf' leafx)
    (hw : Expr.WScoped (d + k) leafx) :
    SimC mode env s₀
      (fun (v : Option PropWhen) (vx : Option PropWhen) => v = vx)
      (annotatePisPwI mode (coreKnotI mode (mkFEnv env) f) d k leaf')
      (annotatePisPw mode (fueledFns mode env) env d k leafx) := by
  unfold annotatePisPwI annotatePisPw
  split
  · refine SimC.bind (annotPwPiC_sim ih hs hl hw)
      (fun s₁ p px hs₁ hP => ?_)
    subst hP
    exact SimC.pure hs₁ rfl
  · exact SimC.pure hs rfl

/-- The λ twin of `annotatePisPwC_sim`. -/
theorem annotateLamsPwC_sim (ih : SSimC mode env f) {d k : Nat}
    {leaf' : ExprC} {leafx : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hl : RelC leaf' leafx)
    (hw : Expr.WScoped (d + k) leafx) :
    SimC mode env s₀
      (fun (v : Option PropWhen) (vx : Option PropWhen) => v = vx)
      (annotateLamsPwI mode (coreKnotI mode (mkFEnv env) f) d k leaf')
      (annotateLamsPw mode (fueledFns mode env) env d k leafx) := by
  unfold annotateLamsPwI annotateLamsPw
  split
  · refine SimC.bind (annotPwLamC_sim ih hs hl hw)
      (fun s₁ p px hs₁ hP => ?_)
    subst hP
    exact SimC.pure hs₁ rfl
  · exact SimC.pure hs rfl

theorem annotatePisLeafC_sim (ih : SSimC mode env f) {d : Nat}
    {t : ExprC} {tx : Expr} {k : Nat} {fvs : Array ExprC} {ws : List Expr}
    {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
    {s₀ : CState}
    (hs : CSOK mode env s₀) (ht : RelC t tx)
    (hfvs : RelCL fvs.toList.reverse ws) (hstk : RelAStk d stk stkx (k - 1))
    (hw : Expr.WScoped (d + k) (tx.instantiateList ws)) :
    SimC mode env s₀ RelDC
      (annotatePisLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      (annotatePisLeaf mode (fueledFns mode env) env d tx k ws stkx) := by
  unfold annotatePisLeafI annotatePisLeaf
  refine SimC.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hQob => ?_)
  refine SimC.bind (ih.annotate hs₁ hQob hw)
    (fun s₂ leaf' leafx hs₂ hPl => ?_)
  obtain ⟨hld, hwl⟩ := hPl
  -- task #161 P5: the telescope's datum, computed once on the annotated
  -- residual, then threaded outward by the rebuild fold
  refine SimC.bind (annotatePisPwC_sim ih hs₂ hld hwl)
    (fun s₄ pw? pw?x hs₄ hPpw => ?_)
  subst hPpw
  refine SimC.bind_left (abstractRangeM_eff hs₄ hld)
    (fun s₅ cur hs₅ hQcur => ?_)
  refine annotateBindersOutC_sim ?_ hs₅ hstk hQcur
  exact fun _n ty tyx b bx _mi hty hb => ⟨⟨hty.1, hb.1⟩, by
    dsimp only [eraseCV, ofViewE]
    rw [hty.2, hb.2]⟩

theorem annotatePisC_sim (ih : SSimC mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : ExprC} {tx : Expr} {k : Nat}
      {fvs : Array ExprC} {ws : List Expr}
      {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {s₀ : CState},
      CSOK mode env s₀ → RelC t tx →
      RelCL fvs.toList.reverse ws → RelAStk d stk stkx (k - 1) →
      Expr.WScoped (d + k) (tx.instantiateList ws) →
      SimC mode env s₀ RelDC
        (annotatePisI mode (coreKnotI mode (mkFEnv env) f) d fuel t k fvs
          stk)
        (annotatePis mode (fueledFns mode env) env d fuel tx k ws stkx)
  | 0, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    exact annotatePisLeafC_sim ih hs ht hfvs hstk hw
  | fuel + 1, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    show SimC mode env s₀ RelDC
      (do
        match ← viewI t with
        | some (.forallE n ty body mb) => do
          let tyo ← instListRevM ty fvs
          let ty' ← (coreKnotI mode (mkFEnv env) f).annotate (d + k) tyo
          let fv ← internI (.fvar (d + k) n ty')
          annotatePisI mode (coreKnotI mode (mkFEnv env) f) d fuel body
            (k + 1) (fvs.push fv) ((n, ty', mb) :: stk)
        | _ =>
          annotatePisLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs
            stk)
      _
    refine SimC.view ?_
    have ht' := ht
    obtain ⟨hwc, rfl⟩ := ht
    cases t
    case forallE nm ty body mb =>
      dsimp only [ExprC.view] at hw ⊢
      rw [annotatePis_succ_pi]
      obtain ⟨hwty, hwbody, -⟩ := hwc.forallE_inv
      have hpiL : (Expr.forallE nm ty body mb).instantiateList
          ws = Expr.forallE nm ((Expr.instantiateList ty ws))
            ((Expr.instantiateList body ws 1)) mb := by
        simp [Expr.instantiateList]
      have hwcomp : Expr.WScoped (d + k) ((Expr.instantiateList ty ws))
          ∧ Expr.WScoped (d + k) ((Expr.instantiateList body ws 1)) := by
        rw [hpiL] at hw
        simpa only [Expr.WScoped] using hw
      refine SimC.bind_left
        (instListRevM_eff (d := 0) hs ⟨hwty, rfl⟩ hfvs)
        (fun s₁ tyo hs₁ hQtyo => ?_)
      refine SimC.bind (ih.annotate hs₁ hQtyo hwcomp.1)
        (fun s₂ ty' tyx' hs₂ hPty' => ?_)
      obtain ⟨hty'd, hwty'⟩ := hPty'
      refine SimC.bind_left
        (internI_eff hs₂ (n := ExprView.fvar (d + k) nm ty') hty'd.1)
        (fun s₃ fv hs₃ hQfv => ?_)
      have hQfv' : RelC fv (Expr.fvar (d + k) nm tyx') := by
        refine ⟨hQfv.1, ?_⟩
        rw [show fv = .fvar (d + k) nm ty' from hQfv.2,
          hty'd.2]
      have hwopen : Expr.WScoped (d + (k + 1))
          ((Expr.instantiateList body (Expr.fvar (d + k) nm tyx' :: ws))) := by
        rw [Expr.instantiateList_cons]
        have := Expr.WScoped.instantiate1 (n := nm) hwty' 0 hwcomp.2
        simpa [Nat.add_assoc] using this
      refine annotatePisC_sim ih fuel hs₃ ⟨hwbody, rfl⟩
        (by rw [toListRev_push]
            exact RelCL.cons hQfv' hfvs)
        ⟨⟨rfl, rfl, hty'd, (by simpa using hwty')⟩, (by simpa using hstk)⟩
        hwopen
    all_goals
      dsimp only [ExprC.view]
      rw [annotatePis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotatePisLeafC_sim ih hs ht' hfvs hstk hw

/-! ## The λ-annotation loop walks -/

theorem annotateLamsLeafC_sim (ih : SSimC mode env f) {d : Nat}
    {t : ExprC} {tx : Expr} {k : Nat} {fvs : Array ExprC} {ws : List Expr}
    {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
    {s₀ : CState}
    (hs : CSOK mode env s₀) (ht : RelC t tx)
    (hfvs : RelCL fvs.toList.reverse ws) (hstk : RelAStk d stk stkx (k - 1))
    (hw : Expr.WScoped (d + k) (tx.instantiateList ws)) :
    SimC mode env s₀ RelDC
      (annotateLamsLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      (annotateLamsLeaf mode (fueledFns mode env) env d tx k ws stkx) := by
  unfold annotateLamsLeafI annotateLamsLeaf
  refine SimC.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hQob => ?_)
  refine SimC.bind (ih.annotate hs₁ hQob hw)
    (fun s₂ leaf' leafx hs₂ hPl => ?_)
  obtain ⟨hld, hwl⟩ := hPl
  -- task #161 P5: the telescope's datum, computed once on the annotated
  -- residual, then threaded outward by the rebuild fold
  refine SimC.bind (annotateLamsPwC_sim ih hs₂ hld hwl)
    (fun s₄ pw? pw?x hs₄ hPpw => ?_)
  subst hPpw
  refine SimC.bind_left (abstractRangeM_eff hs₄ hld)
    (fun s₆ cur hs₆ hQcur => ?_)
  refine annotateBindersOutC_sim ?_ hs₆ hstk hQcur
  exact fun _n ty tyx b bx _mi hty hb => ⟨⟨hty.1, hb.1⟩, by
    dsimp only [eraseCV, ofViewE]
    rw [hty.2, hb.2]⟩

theorem annotateLamsC_sim (ih : SSimC mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : ExprC} {tx : Expr} {k : Nat}
      {fvs : Array ExprC} {ws : List Expr}
      {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {s₀ : CState},
      CSOK mode env s₀ → RelC t tx →
      RelCL fvs.toList.reverse ws → RelAStk d stk stkx (k - 1) →
      Expr.WScoped (d + k) (tx.instantiateList ws) →
      SimC mode env s₀ RelDC
        (annotateLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel t k fvs
          stk)
        (annotateLams mode (fueledFns mode env) env d fuel tx k ws stkx)
  | 0, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    exact annotateLamsLeafC_sim ih hs ht hfvs hstk hw
  | fuel + 1, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    show SimC mode env s₀ RelDC
      (do
        match ← viewI t with
        | some (.lam n ty body mb) => do
          let tyo ← instListRevM ty fvs
          let ty' ← (coreKnotI mode (mkFEnv env) f).annotate (d + k) tyo
          let fv ← internI (.fvar (d + k) n ty')
          annotateLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel body
            (k + 1) (fvs.push fv) ((n, ty', mb) :: stk)
        | _ =>
          annotateLamsLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs
            stk)
      _
    refine SimC.view ?_
    have ht' := ht
    obtain ⟨hwc, rfl⟩ := ht
    cases t
    case lam nm ty body mb =>
      dsimp only [ExprC.view] at hw ⊢
      rw [annotateLams_succ_lam]
      obtain ⟨hwty, hwbody, -⟩ := hwc.lam_inv
      have hlamL : (Expr.lam nm ty body mb).instantiateList
          ws = Expr.lam nm ((Expr.instantiateList ty ws))
            ((Expr.instantiateList body ws 1)) mb := by
        simp [Expr.instantiateList]
      have hwcomp : Expr.WScoped (d + k) ((Expr.instantiateList ty ws))
          ∧ Expr.WScoped (d + k) ((Expr.instantiateList body ws 1)) := by
        rw [hlamL] at hw
        simpa only [Expr.WScoped] using hw
      refine SimC.bind_left
        (instListRevM_eff (d := 0) hs ⟨hwty, rfl⟩ hfvs)
        (fun s₁ tyo hs₁ hQtyo => ?_)
      refine SimC.bind (ih.annotate hs₁ hQtyo hwcomp.1)
        (fun s₂ ty' tyx' hs₂ hPty' => ?_)
      obtain ⟨hty'd, hwty'⟩ := hPty'
      refine SimC.bind_left
        (internI_eff hs₂ (n := ExprView.fvar (d + k) nm ty') hty'd.1)
        (fun s₃ fv hs₃ hQfv => ?_)
      have hQfv' : RelC fv (Expr.fvar (d + k) nm tyx') := by
        refine ⟨hQfv.1, ?_⟩
        rw [show fv = .fvar (d + k) nm ty' from hQfv.2,
          hty'd.2]
      have hwopen : Expr.WScoped (d + (k + 1))
          ((Expr.instantiateList body (Expr.fvar (d + k) nm tyx' :: ws))) := by
        rw [Expr.instantiateList_cons]
        have := Expr.WScoped.instantiate1 (n := nm) hwty' 0 hwcomp.2
        simpa [Nat.add_assoc] using this
      refine annotateLamsC_sim ih fuel hs₃ ⟨hwbody, rfl⟩
        (by rw [toListRev_push]
            exact RelCL.cons hQfv' hfvs)
        ⟨⟨rfl, rfl, hty'd, (by simpa using hwty')⟩, (by simpa using hstk)⟩
        hwopen
    all_goals
      dsimp only [ExprC.view]
      rw [annotateLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotateLamsLeafC_sim ih hs ht' hfvs hstk hw

/-! ## Tail compositions: the annotation loops against the chained
bodies' own tails

As with the infer tails, the two `*_atF` normalizations are pure
comparand-side lemmas, byte-identical copies of `BinderLoopI`'s private
originals (the cached tier does not import the interned walks). -/

private theorem annPiTail_atF {env : Env} (d : Nat) (nm : Name)
    (tyx' bodyx : Expr) (mx : BinderMeta) (F : Nat) :
    ((do
      let body' ← (fueledFns mode env).annotate (d + 1)
        (bodyx.instantiate1 (.fvar d nm tyx'))
      if mode.verified && !pwWritten mx.pw then
        annotPwPi (fueledFns mode env) env (d + 1) body' >>= fun pw =>
          pure (Expr.forallE nm tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩)
      else pure (Expr.forallE nm tyx' (body'.abstract1 d) ⟨mx.bi, mx.pw⟩))
      : FueledM Expr).val F
    = (annotateCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d nm tyx'))
        >>= fun body' =>
        if mode.verified && !pwWritten mx.pw then
          annotPwPi (pureFns mode env F) env (d + 1) body' >>= fun pw =>
            pure (Expr.forallE nm tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩)
        else pure (Expr.forallE nm tyx' (body'.abstract1 d)
          ⟨mx.bi, mx.pw⟩)) := by
  rw [FueledM.atF_bind]
  congr 1
  funext body'
  simp only [FueledM.atF_ite]
  split
  · rw [FueledM.atF_bind, annotPwPi_atF]
    rfl
  · rfl

/-- The ∀-annotation loop against `annotateBody`'s own ∀-tail (pure
post-erasure: the pass computes nothing at binders). -/
theorem annotatePisC_tail_sim (ih : SSimC mode env f) {d fuel : Nat}
    {b ty' fv : ExprC} {bodyx tyx' : Expr} {nm nmx : Name}
    {mi mx : BinderMeta} {s₀ : CState}
    (hs : CSOK mode env s₀)
    (hnm : nm = nmx)
    (hbm : mi = mx)
    (hbody : RelC b bodyx)
    (hty' : RelC ty' tyx')
    (hfv : RelC fv (.fvar d nmx tyx'))
    (hwty' : Expr.WScoped d tyx') (hwbody : Expr.WScoped d bodyx) :
    SimC mode env s₀ (RelEC d)
      (annotatePisI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', mi)])
      (do
        let body' ← (fueledFns mode env).annotate (d + 1)
          (bodyx.instantiate1 (.fvar d nmx tyx'))
        if mode.verified && !pwWritten mx.pw then
          annotPwPi (fueledFns mode env) env (d + 1) body' >>= fun pw =>
            pure (Expr.forallE nmx tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩)
        else pure (Expr.forallE nmx tyx' (body'.abstract1 d)
          ⟨mx.bi, mx.pw⟩)) := by
  have hwopen : Expr.WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nmx tyx']) := by
    rw [instList_single]
    exact Expr.WScoped.instantiate1 hwty' 0 hwbody
  have hcore : SimC mode env s₀ RelDC
      (annotatePisI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', mi)])
      (annotatePis mode (fueledFns mode env) env d fuel bodyx 1
        [Expr.fvar d nmx tyx'] [(nmx, tyx', mx)]) := by
    refine annotatePisC_sim ih fuel hs hbody
      (by rw [toListRev_singleton]; exact RelCL.cons hfv RelCL.nil)
      ⟨⟨hnm, hbm, hty', (hwty' : Expr.WScoped (d + 0) tyx')⟩, trivial⟩ hwopen
  refine SimC.wp (SimC.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [annotatePis_atF] at hF
    obtain ⟨F', hchain⟩ := annotatePis_sound fuel bodyx 1
      [Expr.fvar d nmx tyx'] [(nmx, tyx', mx)] F res rfl hF
    refine ⟨F', ?_⟩
    rw [annPiTail_atF]
    obtain ⟨body', hbody', hwrap⟩ := bind_okB hchain
    have hbody'' : annotateCore mode env F' (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx')) = .ok body' := by
      rw [← instList_single bodyx (Expr.fvar d nmx tyx')]
      exact hbody'
    rw [hbody'', okB_bind]
    -- the chained tail at a one-entry stack IS `annotateBody`'s own
    -- ∀/λ clause: one write, then the rebuilt node (task #161 P5)
    rw [annotatePisWrap_cons] at hwrap
    simpa only [annotatePisWrap_nil, show (1 : Nat) - 1 = 0 from rfl,
      Nat.add_zero] using hwrap
  case hsc =>
    intro v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [annPiTail_atF] at hF
    obtain ⟨body', hbody', hF⟩ := bind_okB hF
    have hwb : Expr.WScoped (d + 1) body' :=
      annotateCore_WScoped F _ hbody'
        (Expr.WScoped.instantiate1 hwty' 0 hwbody)
    -- the node's scoping does not depend on the written datum
    have hnode : ∀ pw : PropWhen,
        Expr.WScoped d
          (Expr.forallE nmx tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩) :=
      fun _ => by
        simp only [Expr.WScoped]
        exact ⟨hwty', Setlec.WScoped.abstract1 0 hwb⟩
    revert hF
    split
    · intro hF
      obtain ⟨pw, -, hF⟩ := bind_okB hF
      injection hF with hres
      exact hres ▸ hnode pw
    · intro hF
      injection hF with hres
      exact hres ▸ hnode mx.pw

private theorem annLamTail_atF {env : Env} (d : Nat) (nmx : Name)
    (tyx' bodyx : Expr) (mx : BinderMeta) (F : Nat) :
    ((do
      let body' ← (fueledFns mode env).annotate (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx'))
      if mode.verified && !pwWritten mx.pw then
        annotPwLam (fueledFns mode env) env (d + 1) body' >>= fun pw =>
          pure (Expr.lam nmx tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩)
      else pure (Expr.lam nmx tyx' (body'.abstract1 d) ⟨mx.bi, mx.pw⟩))
      : FueledM Expr).val F
    = (annotateCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d nmx tyx'))
        >>= fun body' =>
        if mode.verified && !pwWritten mx.pw then
          annotPwLam (pureFns mode env F) env (d + 1) body' >>= fun pw =>
            pure (Expr.lam nmx tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩)
        else pure (Expr.lam nmx tyx' (body'.abstract1 d)
          ⟨mx.bi, mx.pw⟩)) := by
  rw [FueledM.atF_bind]
  congr 1
  funext body'
  simp only [FueledM.atF_ite]
  split
  · rw [FueledM.atF_bind, annotPwLam_atF]
    rfl
  · rfl

/-- The λ-annotation loop against `annotateBody`'s own λ-tail. -/
theorem annotateLamsC_tail_sim (ih : SSimC mode env f) {d fuel : Nat}
    {b ty' fv : ExprC} {bodyx tyx' : Expr} {nm nmx : Name}
    {mi mx : BinderMeta} {s₀ : CState}
    (hs : CSOK mode env s₀)
    (hnm : nm = nmx)
    (hbm : mi = mx)
    (hbody : RelC b bodyx)
    (hty' : RelC ty' tyx')
    (hfv : RelC fv (.fvar d nmx tyx'))
    (hwty' : Expr.WScoped d tyx') (hwbody : Expr.WScoped d bodyx) :
    SimC mode env s₀ (RelEC d)
      (annotateLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', mi)])
      (do
        let body' ← (fueledFns mode env).annotate (d + 1)
          (bodyx.instantiate1 (.fvar d nmx tyx'))
        if mode.verified && !pwWritten mx.pw then
          annotPwLam (fueledFns mode env) env (d + 1) body' >>= fun pw =>
            pure (Expr.lam nmx tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩)
        else pure (Expr.lam nmx tyx' (body'.abstract1 d)
          ⟨mx.bi, mx.pw⟩)) := by
  have hwopen : Expr.WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nmx tyx']) := by
    rw [instList_single]
    exact Expr.WScoped.instantiate1 hwty' 0 hwbody
  have hcore : SimC mode env s₀ RelDC
      (annotateLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', mi)])
      (annotateLams mode (fueledFns mode env) env d fuel bodyx 1
        [Expr.fvar d nmx tyx'] [(nmx, tyx', mx)]) := by
    refine annotateLamsC_sim ih fuel hs hbody
      (by rw [toListRev_singleton]; exact RelCL.cons hfv RelCL.nil)
      ⟨⟨hnm, hbm, hty', (hwty' : Expr.WScoped (d + 0) tyx')⟩, trivial⟩ hwopen
  refine SimC.wp (SimC.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [annotateLams_atF] at hF
    obtain ⟨F', hchain⟩ := annotateLams_sound fuel bodyx 1
      [Expr.fvar d nmx tyx'] [(nmx, tyx', mx)] F res rfl hF
    refine ⟨F', ?_⟩
    rw [annLamTail_atF]
    obtain ⟨body', hbody', hwrap⟩ := bind_okB hchain
    have hbody'' : annotateCore mode env F' (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx')) = .ok body' := by
      rw [← instList_single bodyx (Expr.fvar d nmx tyx')]
      exact hbody'
    rw [hbody'', okB_bind]
    -- the chained tail at a one-entry stack IS `annotateBody`'s own
    -- ∀/λ clause: one write, then the rebuilt node (task #161 P5)
    rw [annotateLamsWrap_cons] at hwrap
    simpa only [annotateLamsWrap_nil, show (1 : Nat) - 1 = 0 from rfl,
      Nat.add_zero] using hwrap
  case hsc =>
    intro v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [annLamTail_atF] at hF
    obtain ⟨body', hbody', hF⟩ := bind_okB hF
    have hwb : Expr.WScoped (d + 1) body' :=
      annotateCore_WScoped F _ hbody'
        (Expr.WScoped.instantiate1 hwty' 0 hwbody)
    -- the node's scoping does not depend on the written datum
    have hnode : ∀ pw : PropWhen,
        Expr.WScoped d (Expr.lam nmx tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩) :=
      fun _ => by
        simp only [Expr.WScoped]
        exact ⟨hwty', Setlec.WScoped.abstract1 0 hwb⟩
    revert hF
    split
    · intro hF
      obtain ⟨pw, -, hF⟩ := bind_okB hF
      injection hF with hres
      exact hres ▸ hnode pw
    · intro hF
      injection hF with hres
      exact hres ▸ hnode mx.pw

end Setlec.Cached
